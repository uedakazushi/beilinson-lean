/-!
# Optional Axiom Stacks integration probe

This is deliberately NOT imported by the default Beilinson/Book targets.
The upstream Stacks codebase is very large. Import this focused module
to check access to an algebraic-geometric derived result without
loading the entire `Stacks` umbrella module.

A successful build checks compatibility of this import, not the
Beilinson theorem or mathematical applicability of any particular lemma.
-/
import StacksFrontier.AlgebraicGeometry.AffineDerivedBaseChange

namespace Beilinson.StacksProbe

end Beilinson.StacksProbe
