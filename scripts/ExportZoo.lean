/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Registry

/-!
# Zoo export script

Run via `lake env lean scripts/ExportZoo.lean` (from the project root; done by
`rmlib-zoo build` and CI). An elaboration script rather than a compiled executable on purpose:
the imported persistent-extension state is naturally present in the elaboration environment,
exactly as for `#revmath_registry`.
-/

#rm_export_catalog ".lake/build/zoo/catalog.direct.json"
