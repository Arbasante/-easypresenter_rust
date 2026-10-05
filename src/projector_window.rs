//! Native projection-window policy, applied before the window is mapped.
use slint::winit_030::{WinitWindowAccessor, winit};
use std::cell::Cell;

thread_local! {
    static CREATING_PROJECTOR: Cell<bool> = const { Cell::new(false) };
}

pub fn initialize_backend() -> Result<(), slint::PlatformError> {
    let backend = slint::BackendSelector::new()
        .backend_name("winit".into())
        .with_winit_window_attributes_hook(|attributes| {
            if !CREATING_PROJECTOR.get() {
                return attributes;
            }
            #[cfg(target_os = "windows")]
            {
                use winit::platform::windows::WindowAttributesExtWindows;
                attributes.with_skip_taskbar(true)
            }
            #[cfg(target_os = "linux")]
            {
                use winit::platform::x11::{WindowAttributesExtX11, WindowType};
                attributes.with_x11_window_type(vec![WindowType::Utility])
            }
            #[cfg(not(any(target_os = "windows", target_os = "linux")))]
            attributes
        });
    // Native Wayland has no portable skip-taskbar/skip-switcher request.
    // Use X11 (XWayland on Wayland desktops), which also supports projection positioning.
    #[cfg(target_os = "linux")]
    let backend = {
        use winit::platform::x11::EventLoopBuilderExtX11;
        let mut builder =
            winit::event_loop::EventLoop::<slint::winit_030::SlintEvent>::with_user_event();
        builder.with_x11();
        backend.with_winit_event_loop_builder(builder)
    };
    backend.select()
}

pub fn create() -> Result<crate::ProjectorWindow, slint::PlatformError> {
    struct Reset(bool);
    impl Drop for Reset {
        fn drop(&mut self) {
            CREATING_PROJECTOR.set(self.0);
        }
    }
    let _reset = Reset(CREATING_PROJECTOR.replace(true));
    let projector = crate::ProjectorWindow::new()?;
    #[cfg(target_os = "windows")]
    {
        // winit can replace extended styles when showing/maximizing the window.
        // Restore our policy on subsequent native events as well.
        use slint::ComponentHandle;
        projector.window().on_winit_window_event(|window, _| {
            window.with_winit_window(|native| {
                if let Err(error) = prepare_native(native) {
                    eprintln!("No se pudo mantener el estilo del proyector: {error}");
                }
            });
            slint::winit_030::EventResult::Propagate
        });
    }
    Ok(projector)
}

pub async fn prepare(window: &slint::Window) -> Result<(), Box<dyn std::error::Error>> {
    // Slint creates native windows lazily. Obtain an unmapped native window first.
    let native = window.winit_window().await?;
    prepare_native(&native)
}

#[cfg(target_os = "windows")]
pub fn fullscreen_on_monitor(
    window: &slint::Window,
    target: Option<(i32, i32)>,
) -> Result<(), Box<dyn std::error::Error>> {
    use winit::raw_window_handle::{HasWindowHandle, RawWindowHandle};
    use winit::window::{Fullscreen, WindowLevel};
    window.set_maximized(false);
    window
        .with_winit_window(|native| -> Result<(), Box<dyn std::error::Error>> {
            let monitor = if let Some((x, y)) = target {
                // DisplayInfo identifies the target; winit supplies its physical bounds.
                // Do not multiply monitor.size() by the DPI scale factor again.
                native.available_monitors().min_by_key(|monitor| {
                    let position = monitor.position();
                    let dx = i128::from(position.x) - i128::from(x);
                    let dy = i128::from(position.y) - i128::from(y);
                    dx * dx + dy * dy
                })
            } else {
                native
                    .current_monitor()
                    .or_else(|| native.primary_monitor())
            }
            .ok_or("No se encontró el monitor de proyección")?;
            let position = monitor.position();
            let size = monitor.size();
            native.set_decorations(false);
            native.set_window_level(WindowLevel::AlwaysOnTop);
            native.set_fullscreen(Some(Fullscreen::Borderless(Some(monitor))));
            window.set_fullscreen(true);
            prepare_native(native)?;

            let RawWindowHandle::Win32(handle) = native.window_handle()?.as_raw() else {
                return Err("La proyección no tiene un HWND de Windows".into());
            };
            #[link(name = "user32")]
            unsafe extern "system" {
                fn SetWindowPos(
                    hwnd: isize,
                    after: isize,
                    x: i32,
                    y: i32,
                    width: i32,
                    height: i32,
                    flags: u32,
                ) -> i32;
            }
            const HWND_TOPMOST: isize = -1;
            const SWP_NOACTIVATE: u32 = 0x10;
            const SWP_FRAMECHANGED: u32 = 0x20;
            // SAFETY: valid HWND owned by winit, on the UI thread. These are full
            // monitor bounds in physical pixels, including the taskbar region.
            if unsafe {
                SetWindowPos(
                    handle.hwnd.get(),
                    HWND_TOPMOST,
                    position.x,
                    position.y,
                    i32::try_from(size.width)?,
                    i32::try_from(size.height)?,
                    SWP_NOACTIVATE | SWP_FRAMECHANGED,
                )
            } == 0
            {
                return Err(std::io::Error::last_os_error().into());
            }
            Ok(())
        })
        .ok_or("La ventana nativa del proyector no está disponible")?
}

#[cfg(target_os = "linux")]
fn prepare_native(window: &winit::window::Window) -> Result<(), Box<dyn std::error::Error>> {
    use winit::raw_window_handle::{HasWindowHandle, RawWindowHandle};
    use x11rb::{
        connection::Connection,
        protocol::xproto::{AtomEnum, ConnectionExt, PropMode},
        wrapper::ConnectionExt as _,
    };
    let id = match window.window_handle()?.as_raw() {
        RawWindowHandle::Xlib(handle) => u32::try_from(handle.window)?,
        RawWindowHandle::Xcb(handle) => handle.window.get(),
        _ => return Err("La proyección sin barra de tareas requiere X11/XWayland".into()),
    };
    let (connection, _) = x11rb::connect(None)?;
    let atom = |name: &[u8]| -> Result<u32, Box<dyn std::error::Error>> {
        Ok(connection.intern_atom(false, name)?.reply()?.atom)
    };
    let state = atom(b"_NET_WM_STATE")?;
    let mut states: Vec<u32> = connection
        .get_property(false, id, state, AtomEnum::ATOM, 0, u32::MAX)?
        .reply()?
        .value32()
        .map(|values| values.collect())
        .unwrap_or_default();
    for name in [
        b"_NET_WM_STATE_SKIP_TASKBAR".as_slice(),
        b"_NET_WM_STATE_SKIP_PAGER".as_slice(),
    ] {
        let value = atom(name)?;
        if !states.contains(&value) {
            states.push(value);
        }
    }
    connection
        .change_property32(PropMode::REPLACE, id, state, AtomEnum::ATOM, &states)?
        .check()?;
    connection
        .change_property32(
            PropMode::REPLACE,
            id,
            atom(b"_NET_WM_WINDOW_TYPE")?,
            AtomEnum::ATOM,
            &[atom(b"_NET_WM_WINDOW_TYPE_UTILITY")?],
        )?
        .check()?;
    connection.flush()?;
    Ok(())
}

#[cfg(target_os = "windows")]
fn prepare_native(window: &winit::window::Window) -> Result<(), Box<dyn std::error::Error>> {
    use winit::platform::windows::WindowExtWindows;
    use winit::raw_window_handle::{HasWindowHandle, RawWindowHandle};
    let RawWindowHandle::Win32(handle) = window.window_handle()?.as_raw() else {
        return Err("La proyección no tiene un HWND de Windows".into());
    };
    #[link(name = "user32")]
    unsafe extern "system" {
        #[cfg_attr(target_pointer_width = "64", link_name = "GetWindowLongPtrW")]
        #[cfg_attr(target_pointer_width = "32", link_name = "GetWindowLongW")]
        fn get_style(hwnd: isize, index: i32) -> isize;
        #[cfg_attr(target_pointer_width = "64", link_name = "SetWindowLongPtrW")]
        #[cfg_attr(target_pointer_width = "32", link_name = "SetWindowLongW")]
        fn set_style(hwnd: isize, index: i32, value: isize) -> isize;
        fn SetWindowPos(
            hwnd: isize,
            after: isize,
            x: i32,
            y: i32,
            width: i32,
            height: i32,
            flags: u32,
        ) -> i32;
    }
    const GWL_EXSTYLE: i32 = -20;
    const WS_EX_TOOLWINDOW: isize = 0x80;
    const WS_EX_APPWINDOW: isize = 0x40000;
    let hwnd = handle.hwnd.get();
    // SAFETY: winit owns this valid HWND; called on its UI thread before showing it.
    unsafe {
        let current_style = get_style(hwnd, GWL_EXSTYLE);
        let style = (current_style | WS_EX_TOOLWINDOW) & !WS_EX_APPWINDOW;
        if current_style == style {
            return Ok(());
        }
        set_style(hwnd, GWL_EXSTYLE, style);
        if get_style(hwnd, GWL_EXSTYLE) & (WS_EX_TOOLWINDOW | WS_EX_APPWINDOW) != WS_EX_TOOLWINDOW {
            return Err(std::io::Error::last_os_error().into());
        }
        // Refresh styles without moving, resizing, activating or changing the z-order.
        if SetWindowPos(hwnd, 0, 0, 0, 0, 0, 0x37) == 0 {
            return Err(std::io::Error::last_os_error().into());
        }
    }
    window.set_skip_taskbar(true);
    Ok(())
}

#[cfg(not(any(target_os = "windows", target_os = "linux")))]
fn prepare_native(_: &winit::window::Window) -> Result<(), Box<dyn std::error::Error>> {
    Ok(())
}
