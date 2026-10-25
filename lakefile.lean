import Lake
open Lake DSL

package «lean-native» where
  version := v!"0.1.0"

require «lean-sys» from git
  "https://github.com/Th0rgal/lean-sys.git" @ "d5faf5595d99a3b36d07a7d5cd0f10b80133453d"

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
