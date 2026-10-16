#!/usr/bin/env bash
set -euo pipefail

# Only installation resources belong in the package, never personal config or tokens.
destination=${1:?Usage: stage.sh DESTINATION}
install -Dm755 target/release/ReadyShow "$destination/usr/bin/ReadyShow"
for database in cantos.db biblias.db biblias.db.gz; do
    install -Dm644 "data/$database" "$destination/usr/share/readyshow/data/$database"
done
install -Dm755 libpdfium.so "$destination/usr/share/readyshow/libpdfium.so"
install -Dm644 assets/ReadyShow.desktop "$destination/usr/share/applications/ReadyShow.desktop"
for size in 16 24 32 48 64 128 256 512; do
    icon="icons/hicolor/${size}x${size}/apps/ReadyShow.png"
    install -Dm644 "assets/$icon" "$destination/usr/share/$icon"
done
