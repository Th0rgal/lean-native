import Lake
open Lake DSL

package «lean-native» where
  version := v!"0.1.0"

require «lean-sys» from git
  "https://github.com/Th0rgal/lean-sys.git" @ "7ad93dd6db5bff6762242e1131a127364bd41ba8"

lean_lib «LeanNative» where
  roots := #[`LeanNative]

lean_lib «LeanNativeCore» where
  roots := #[`LeanNative.Core]

@[default_target]
lean_exe «lean-native» where
  root := `LeanNative.Driver.Main
  supportInterpreter := true

lean_exe «lean-native-core» where
  root := `LeanNative.Driver.CoreMain
  supportInterpreter := false
