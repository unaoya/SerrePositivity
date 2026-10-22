module

public import SerrePositivity.InfinityCategories.F2.Idempotent.StrongSplittingExistence
public import SerrePositivity.InfinityCategories.Core.FunctorComposition
public import SerrePositivity.InfinityCategories.Stable.ColimitDiagramIso

/-!
概要：元の coherent 冪等完備性は ∞ 圏の同値で保たれる。
方針：逆関手で元の全図式を強く分裂し、絶対余極限と元の可逆二胞体で戻す。
規約：全図式を扱い、ホモトピー圏の自己射の分裂だけで代用しない。
使われ方：元の充満忠実な像への移送と本質像の retract 閉性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の全図式の coherent 冪等完備性を、指定した元の ∞ 圏同値で移す。 -/
lemma IsIdempotentComplete.of_equivalence {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (hX : IsIdempotentComplete X)
    (e : QCatEquivalence X Y) : IsIdempotentComplete Y := by
  intro d
  obtain ⟨s⟩ := hX (d ≫ e.inv)
  have hs : HasColimit ((d ≫ e.inv) ≫ e.hom) := (s.map e.hom).hasColimit
  have hd : FunctorIso ((d ≫ e.inv) ≫ e.hom) d := by
    simpa only [Category.assoc, Category.comp_id] using e.invHomIso.precomp d
  exact strongSplitting_exists_of_hasColimit d ((hasColimit_iff_of_functorIso hd).mp hs)

/-- 指定した元の ∞ 圏同値は、coherent 冪等完備性を保存・反映する。 -/
lemma isIdempotentComplete_iff_of_equivalence {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y) :
    IsIdempotentComplete X ↔ IsIdempotentComplete Y :=
  ⟨fun h ↦ h.of_equivalence e, fun h ↦ h.of_equivalence e.symm⟩

end SerrePositivity.InfinityCategories.F2.Idempotent
