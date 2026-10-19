import Lake
open Lake DSL

package «lean-native» where
  version := v!"0.1.0"

lean_lib «LeanNative» where
  roots := #[`LeanNative]

@[default_target]
lean_exe «lean-native» where
  root := `LeanNative.Driver.Main
  supportInterpreter := true
