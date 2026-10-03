# Repository Guidelines

## Project Structure & Module Organization
ReadyShow (EasyPresenter) is a Rust 2024 desktop application using Slint, SQLite, and GStreamer. Most application logic lives in `src/main.rs`. The `ui/` directory contains the main, projector, and splash Slint views; bundled fonts live in `ui/fonts/`. `build.rs` compiles the main UI and embeds Windows resources. `assets/` holds icons and Linux desktop integration, while `data/` contains databases, configuration, and video thumbnails. Packaging is defined in `Cargo.toml`, `installer.iss`, and `.github/workflows/build.yml`.

## Build, Test, and Development Commands
Run commands from the repository root with stable Rust supporting edition 2024. Install GStreamer development libraries and plugins; consult the build workflow for platform setup. PDF rendering requires the platform PDFium library.

- `cargo run`: launch the desktop application locally.
- `cargo build --release`: produce the optimized executable in `target/release/`.
- `cargo test`: run Rust tests.
- `cargo fmt --check`: check Rust formatting; use `cargo fmt` to apply it.
- `cargo clippy --all-targets`: inspect Rust code for common problems.
- `cargo deb`: build the Linux package after installing `cargo-deb` and preparing packaging resources.

The npm scripts provide placeholder web pages; `npm run lint` only prints a message. Use Cargo for desktop development and validation.

## Coding Style & Naming Conventions
Use four-space indentation and standard rustfmt formatting for Rust. Name functions and variables with `snake_case`, types with `PascalCase`, and constants with `SCREAMING_SNAKE_CASE`. Follow surrounding Slint indentation and property naming. Preserve existing Spanish domain terminology where appropriate. Keep changes focused; avoid formatting unrelated portions of the large main module.

## Testing Guidelines
No dedicated test directory, Rust test cases, or coverage threshold currently exists. Add focused unit tests in `#[cfg(test)]` modules, with descriptive names such as `search_matches_normalized_text`. Run `cargo test` and manually exercise affected desktop workflows, especially projector output, Bible/song lookup, media playback, and PDF rendering.

## Commit & Pull Request Guidelines
History uses Conventional Commit prefixes such as `feat:`, `fix:`, `ci:`, and `chore:`, sometimes with scopes like `feat(ia):`. Follow this pattern with a concise action-oriented subject. Pull requests should explain the behavior change, link relevant issues, record validation and platform tested, and include screenshots for visible UI changes.

## Configuration & Data
Keep API credentials and personal configuration out of commits. Avoid incidental edits to bundled SQLite databases or generated thumbnails; use disposable data for experiments.
