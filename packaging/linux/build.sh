#!/usr/bin/env bash
set -euo pipefail

format=${1:?Usage: build.sh rpm|appimage|flatpak}
version=$(python3 -c 'import tomllib; print(tomllib.load(open("Cargo.toml", "rb"))["package"]["version"])')
mkdir -p dist

case "$format" in
    rpm)
        rpm_root="$PWD/rpm-build"
        mkdir -p "$rpm_root"/{BUILD,BUILDROOT,RPMS,SOURCES,SPECS,SRPMS}
        tar -czf "$rpm_root/SOURCES/readyshow-root.tar.gz" -C package-root usr
        rpmbuild -bb packaging/linux/readyshow.spec \
            --define "_topdir $rpm_root" --define "app_version $version"
        cp "$rpm_root"/RPMS/x86_64/*.rpm dist/
        rpm -qpl dist/*.rpm
        ;;
    appimage)
        mkdir -p appimage-tools
        curl --fail --location --retry 3 \
            https://github.com/linuxdeploy/linuxdeploy/releases/download/continuous/linuxdeploy-x86_64.AppImage \
            -o appimage-tools/linuxdeploy-x86_64.AppImage
        curl --fail --location --retry 3 \
            https://raw.githubusercontent.com/linuxdeploy/linuxdeploy-plugin-gstreamer/master/linuxdeploy-plugin-gstreamer.sh \
            -o appimage-tools/linuxdeploy-plugin-gstreamer.sh
        chmod +x appimage-tools/*
        # Extract instead of requiring FUSE on GitHub-hosted runners.
        export APPIMAGE_EXTRACT_AND_RUN=1
        export PATH="$PWD/appimage-tools:$PATH"
        export VERSION="$version"
        export OUTPUT="$PWD/dist/ReadyShow-$version-x86_64.AppImage"
        appimage-tools/linuxdeploy-x86_64.AppImage \
            --appdir package-root \
            --executable package-root/usr/bin/ReadyShow \
            --library package-root/usr/share/readyshow/libpdfium.so \
            --desktop-file package-root/usr/share/applications/ReadyShow.desktop \
            --icon-file package-root/usr/share/icons/hicolor/256x256/apps/ReadyShow.png \
            --plugin gstreamer --output appimage
        test -s "$OUTPUT"
        ;;
    flatpak)
        flatpak-builder --user --force-clean --disable-rofiles-fuse \
            --install-deps-from=flathub --repo=flatpak-repo \
            flatpak-build packaging/linux/com.arbasante.ReadyShow.yml
        # Check against Platform, not SDK, so build-only libraries cannot hide omissions.
        flatpak build --runtime flatpak-build sh -ec '
            ldd /app/bin/ReadyShow > /tmp/readyshow-ldd
            cat /tmp/readyshow-ldd
            ! grep -q "not found" /tmp/readyshow-ldd
            ldd /app/share/readyshow/libpdfium.so > /tmp/pdfium-ldd
            cat /tmp/pdfium-ldd
            ! grep -q "not found" /tmp/pdfium-ldd
            test -s /app/share/readyshow/data/cantos.db
            test -s /app/share/readyshow/data/biblias.db
        '
        flatpak build-bundle flatpak-repo "dist/ReadyShow-$version-x86_64.flatpak" \
            com.arbasante.ReadyShow master \
            --runtime-repo=https://dl.flathub.org/repo/flathub.flatpakrepo
        ;;
    *)
        echo "Unsupported package format: $format" >&2
        exit 2
        ;;
esac
