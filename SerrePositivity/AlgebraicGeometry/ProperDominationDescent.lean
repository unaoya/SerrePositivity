module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
概要：固有支配による降下で使う、閉埋め込み性と固有性の法則を接続する。
方針：固有射の閉写像性と、普遍閉性の全射合成からの消去を使う。
規約：一般の固有射を扱い、ブローアップや射影射に限定しない。
使われ方：B01・B02 の Stacks 081F による固有性の有限段への降下。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 固有な immersion は閉埋め込み。 -/
theorem isClosedImmersion_of_proper_immersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsImmersion f] [IsProper f] : IsClosedImmersion f :=
  IsClosedImmersion.of_isPreimmersion f f.isClosedMap.isClosed_range

/-- 分離的な周辺の同じ基底上で固有となる immersion は閉埋め込み。 -/
theorem isClosedImmersion_of_proper_over_base {X P S : Scheme.{u}}
    (t : X ⟶ P) [IsImmersion t] (q : P ⟶ S) [IsSeparated q]
    [IsProper (t ≫ q)] : IsClosedImmersion t := by
  haveI : IsProper t := IsProper.of_comp t q
  exact isClosedImmersion_of_proper_immersion t

/-- 全射な支配との合成の固有性は、分離的な有限型射の固有性を反映する。 -/
theorem isProper_of_proper_surjective_comp {T Y S : Scheme.{u}}
    (h : T ⟶ Y) [Surjective h] (f : Y ⟶ S)
    [IsSeparated f] [LocallyOfFiniteType f] [IsProper (h ≫ f)] : IsProper f := by
  haveI : UniversallyClosed f := UniversallyClosed.of_comp_surjective h f
  exact ⟨⟩

end SerrePositivity.AlgebraicGeometry
