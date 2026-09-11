fn main() {
    slint_build::compile("ui/main_ui.slint").unwrap();

    // Solo aplica en compilaciones para Windows
    #[cfg(target_os = "windows")]
    {
        use embed_manifest::{embed_manifest, new_manifest};
        use embed_manifest::manifest::{DpiAwareness, ExecutionLevel};

        let manifest = new_manifest("EasyPresenter.App")
            .dpi_awareness(DpiAwareness::PerMonitorV2)
            .requested_execution_level(ExecutionLevel::AsInvoker);

        embed_manifest(manifest).expect("No se pudo incrustar el manifiesto de Windows");

        // Incrusta el icono de la app en el .exe (ventana, taskbar, inicio, accesos directos)
        let mut res = winres::WindowsResource::new();
        res.set_icon("assets/icon.ico");
        res.compile().expect("No se pudo compilar el recurso de icono de Windows");
    }
}