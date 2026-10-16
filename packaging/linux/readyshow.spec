Name:           readyshow
Version:        %{app_version}
Release:        1
Summary:        Presentaciones multimedia, letras y Biblias
License:        MIT
BuildArch:      x86_64
Source0:        readyshow-root.tar.gz
Requires:       gstreamer1
Requires:       gstreamer1-plugins-base
Requires:       gstreamer1-plugins-good
Requires:       gstreamer1-plugins-bad-free

# The release executable is already stripped by Cargo.
%global debug_package %{nil}
%global _build_id_links none

%description
ReadyShow permite proyectar cantos, versículos, imágenes, videos y documentos PDF.

%prep
%setup -q -c -n readyshow-root

%build
# Compiled once by the build-linux job.

%install
mkdir -p %{buildroot}
cp -a usr %{buildroot}/

%files
/usr/bin/ReadyShow
/usr/share/readyshow
/usr/share/applications/ReadyShow.desktop
/usr/share/icons/hicolor/*/apps/ReadyShow.png
