[Setup]
AppName=EasyPresenter
AppVersion=1.0.0
DefaultDirName={localappdata}\EasyPresenter
DefaultGroupName=EasyPresenter
UninstallDisplayIcon={app}\easy-presenter-slint.exe
Compression=lzma2
SolidCompression=yes
OutputDir=Output
OutputBaseFilename=Instalar_EasyPresenter_v1.0
PrivilegesRequired=lowest

[Files]
Source: "target\release\easy-presenter-slint.exe"; DestDir: "{app}"; Flags: ignoreversion
Source: "data\*";                                  DestDir: "{app}\data"; Flags: ignoreversion recursesubdirs createallsubdirs
Source: "target\release\*.dll";                    DestDir: "{app}"; Flags: ignoreversion
Source: "target\release\lib\*";                    DestDir: "{app}\lib"; Flags: ignoreversion recursesubdirs createallsubdirs

[Registry]
; GStreamer necesita saber dónde están sus plugins (no usa el registro del sistema
; porque es una instalación portable sin el MSI oficial de GStreamer)
Root: HKCU; Subkey: "Environment"; ValueType: string; ValueName: "GST_PLUGIN_PATH"; ValueData: "{app}\lib\gstreamer-1.0"; Flags: uninsdeletevalue

[Icons]
Name: "{autodesktop}\EasyPresenter"; Filename: "{app}\easy-presenter-slint.exe"; WorkingDir: "{app}"
Name: "{group}\EasyPresenter";       Filename: "{app}\easy-presenter-slint.exe"; WorkingDir: "{app}"

[Run]
Filename: "{app}\easy-presenter-slint.exe"; Description: "Lanzar EasyPresenter"; Flags: nowait postinstall skipifsilent