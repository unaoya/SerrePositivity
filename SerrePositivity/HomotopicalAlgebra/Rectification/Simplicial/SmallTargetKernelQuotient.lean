module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.SmallDiagramQuotient
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneKanReplacement
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanFibrationLocalizedLifting

/-!
# 中断した任意モデル源への一般化：SmallTargetKernelQuotient

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual small kernel quotients after an anodyne enlargement。

## 方針（定義・証明）
整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0577][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0577
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual small kernel quotients after an anodyne enlargement

A natural equivalence to lifted small Kan values supplies the relation,
its smallness, and its finite-boundary lifting certificate. The base may
be large. No model structure on either value universe is used.
-/

@[expose] public section
universe v w uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.SmallTargetKernelQuotient
variable {D : Type uD} [Category.{vD} D] {F : D ⥤ SSet.{max w v}} {K : D ⥤ SSet.{v}}
  (a : F ⟶ K ⋙ SSet.uliftFunctor.{max w v, v})

def arrows : D ⥤ Arrow SSet.{max w v} where
  obj d := Arrow.mk (a.app d)
  map f := Arrow.homMk (F.map f) ((K ⋙ SSet.uliftFunctor).map f) (a.naturality f)
  map_id _ := by ext <;> simp
  map_comp _ _ := by ext <;> simp

abbrev middle : D ⥤ SSet.{max w v} := arrows a ⋙ AnodyneKanReplacement.factorization.Z

def unit : F ⟶ middle a where
  app d := AnodyneKanReplacement.factorization.i.app ((arrows a).obj d)
  naturality {_ _} f := AnodyneKanReplacement.factorization.i.naturality ((arrows a).map f)

def projection : middle a ⟶ K ⋙ SSet.uliftFunctor.{max w v, v} where
  app d := AnodyneKanReplacement.factorization.p.app ((arrows a).obj d)
  naturality {_ _} f := AnodyneKanReplacement.factorization.p.naturality ((arrows a).map f)

lemma factorization : unit a ≫ projection a = a := by
  apply NatTrans.ext
  funext d
  exact AnodyneKanReplacement.factorization.fac_app

lemma unit_anodyne (d : D) : SSet.anodyneExtensions ((unit a).app d) :=
  AnodyneKanReplacement.factorization.hi _

lemma projection_horn_rlp (d : D) : SSet.modelCategoryQuillen.J.rlp ((projection a).app d) :=
  AnodyneKanReplacement.factorization.hp _

variable (hK : ∀ d, SSet.modelCategoryQuillen.J.rlp (terminal.from (K.obj d)))
  (ha : ∀ d, IsIso (AnodyneHomotopy.anodyneQ.map (a.app d)))

include ha in
lemma projection_localized_isIso (d : D) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((projection a).app d)) := by
  let Q := AnodyneHomotopy.anodyneQ.{max w v}
  have : IsIso (Q.map (a.app d)) := ha d
  have : IsIso (Q.map ((unit a).app d)) := Localization.inverts Q _ _ (unit_anodyne a d)
  have he := congrArg Q.map (congr_app (factorization a) d)
  rw [NatTrans.comp_app, Q.map_comp] at he
  have : IsIso (Q.map ((unit a).app d) ≫ Q.map ((projection a).app d)) := he.symm ▸ ha d
  exact (isIso_comp_left_iff _ _).mp this

include hK in
lemma middle_kan (d : D) : SSet.modelCategoryQuillen.J.rlp (terminal.from ((middle a).obj d)) := by
  have h := SSet.modelCategoryQuillen.J.rlp.comp_mem _ _ (projection_horn_rlp a d)
    (UniverseLift.horn_terminal_map.{max w v, v} (hK d))
  have he : (projection a).app d ≫ terminal.from
      (SSet.uliftFunctor.{max w v, v}.obj (K.obj d)) = terminal.from ((middle a).obj d) :=
    terminal.hom_ext _ _
  rwa [he] at h

include hK ha in
lemma projection_mono_rlp (d : D) :
    (MorphismProperty.monomorphisms SSet.{max w v}).rlp ((projection a).app d) :=
  KanFibrationLocalizedLifting.of_localized_isIso _ (projection_horn_rlp a d)
    (UniverseLift.horn_terminal_map.{max w v, v} (hK d)) (projection_localized_isIso a ha d)

def relation : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.Congruence (middle a) := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.kernel (projection a)

lemma quotient_small (d : D) (n : SimplexCategoryᵒᵖ) :
    Small.{v} (Quotient ((relation a).rel d n)) := by
  have : Small.{v} (((K ⋙ SSet.uliftFunctor.{max w v, v}).obj d).obj n) :=
    small_of_injective (f := ULift.down) ULift.down_injective
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.kernel_small (projection a) d n

include hK ha in
lemma projection_surjective (d : D) (n : SimplexCategoryᵒᵖ) :
    Function.Surjective (((projection a).app d).app n) := by
  obtain ⟨s, hs⟩ := MonoRightLiftingContraction.exists_section _ (projection_mono_rlp a hK ha d)
  intro z
  exact ⟨s.app n z, types_congr_hom (congr_app hs n) z⟩

include hK ha in
lemma kernelComparison_isIso : IsIso (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.kernelComparison (projection a)) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.kernelComparison_isIso _ (projection_surjective a hK ha)

include hK ha in
lemma quotient_boundary_rlp (d : D) :
    SSet.modelCategoryQuillen.I.rlp ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.projection (relation a)).app d) := by
  have := kernelComparison_isIso a hK ha
  let c := (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.kernelComparison (projection a)).app d
  have he : (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.projection (relation a)).app d =
      (projection a).app d ≫ inv c := by
    apply (cancel_mono c).mp
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact congr_app (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.kernel_factorization (projection a)) d
  rw [← SSet.rlp_monomorphisms, he]
  exact (MorphismProperty.monomorphisms _).rlp.comp_mem _ _
    (projection_mono_rlp a hK ha d) ((MorphismProperty.monomorphisms _).rlp.of_isIso _)

end SerrePositivity.SimplicialModel.SmallTargetKernelQuotient
