module

public import SerrePositivity.InfinityCategories.F2.Presentable.Supply.SequentialTelescopeShape
public import SerrePositivity.InfinityCategories.F2.Presentable.Supply.PreservedColimitComposition
public import SerrePositivity.InfinityCategories.F2.Presentable.NerveFinalInitialComma
public import SerrePositivity.InfinityCategories.F2.Ind.CofinalUniverseLift
public import SerrePositivity.InfinityCategories.F2.Ind.PreservedPushoutShape
public import SerrePositivity.InfinityCategories.F2.Ind.PreservedColimitBasicShapes
public import SerrePositivity.InfinityCategories.F1.Joins.PointConeSpanIso
public import SerrePositivity.InfinityCategories.F1.Universe.Pushouts
public import SerrePositivity.InfinityCategories.Core.FiniteShapeInduction

/-!
概要：望遠鏡の区間族と離散頂点の保存余極限を、小余積と有限余極限から構成する。
方針：区間族を終点の離散族へ right cofinal に縮約し、形状 pushout の保存定理を使う。
規約：継承待ちの P の二葉へ依存せず、同じ元の余錐の保存を保持する。
使われ方：P-11 の可算列の余積・pushout 表示の余極限側。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：可算区間族の終点の離散族は、全区間族の nerve で right cofinal。
方針：各右 comma の始対象を元の区間の終点で明示する。
規約：単なる通常圏の final 性で止めず、元の nerve の共終性を返す。
使われ方：区間族の保存余極限を小余積へ縮約する。 -/
lemma sequentialTelescopeFinalVertices_isRightCofinal :
    IsRightCofinal (nerveMap
      (CategoryTheory.Prod.sectL (Discrete (ULift.{u} ℕ)) (1 : Fin 2))) := by
  apply nerveMap_isRightCofinal_of_initial_comma
  intro q
  let c : StructuredArrow q
      (CategoryTheory.Prod.sectL (Discrete (ULift.{u} ℕ)) (1 : Fin 2)) :=
    StructuredArrow.mk (Y := q.1) (𝟙 q.1, homOfLE (Fin.le_last q.2))
  refine ⟨c, ⟨IsInitial.ofUniqueHom (fun y ↦ ?_) ?_⟩⟩
  · exact StructuredArrow.homMk y.hom.1 (by
      apply CategoryTheory.Prod.hom_ext <;> exact Subsingleton.elim _ _)
  · intro y f
    apply StructuredArrow.hom_ext
    exact Subsingleton.elim _ _

/-- 概要：区間族上の任意の図式の保存余極限は、終点の小余積から得られる。
方針：終点の right cofinal な包含を宇宙変更し、同じ保存余錐を戻す。
規約：可算列上の共終性はまだ仮定・結論に含めない。
使われ方：望遠鏡の形状 pushout の区間側の入力。 -/
lemma hasPreservedColimit_sequentialTelescopeIntervals
    {X Y : SSet.{u + 1}} [Quasicategory X] [Quasicategory Y] (U : X ⟶ Y)
    (hcop : ∀ (I : Type u)
      (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)) ⟶ X),
      Ind.HasPreservedColimit U D)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj
      (nerve (Discrete (ULift.{u} ℕ) × Fin 2)) ⟶ X) :
    Ind.HasPreservedColimit U F := by
  let i := nerveMap (CategoryTheory.Prod.sectL (Discrete (ULift.{u} ℕ)) (1 : Fin 2))
  have hi := Ind.isRightCofinal_ulift.{u, u + 1} i
    sequentialTelescopeFinalVertices_isRightCofinal
  exact (hasPreservedColimit_iff_rightCofinalRestriction U
    ((SSet.uliftFunctor.{u + 1, u}).map i) hi F).mpr (hcop _ _)

/-- 概要：小余積と有限余極限の保存から、望遠鏡形状の保存余極限を構成する。
方針：離散端点・頂点の小余積、区間族の終点縮約、単射側の形状 pushout を合成する。
規約：可算 nerve への写像の共終性は後続工程に残す。
使われ方：P-11 の可算列の余積・pushout 構成の普遍余錐。 -/
lemma hasPreservedColimit_sequentialTelescopeShape
    {X Y : SSet.{u + 1}} [Quasicategory X] [Quasicategory Y] (U : X ⟶ Y)
    (hcop : ∀ (I : Type u)
      (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)) ⟶ X),
      Ind.HasPreservedColimit U D)
    (hfin : ∀ (K : SSet.{u + 1}) [K.Finite] (D : K ⟶ X), Ind.HasPreservedColimit U D)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj sequentialTelescopeShape.{u} ⟶ X) :
    Ind.HasPreservedColimit U F := by
  let f := nerveMap sequentialTelescopeAttachFunctor.{u}
  let g := nerveMap sequentialTelescopeBoundaryFunctor.{u}
  let L := SSet.uliftFunctor.{u + 1, u}
  have : Mono g := sequentialTelescopeBoundary_mono
  have : Mono (L.map g) := by
    rw [NatTrans.mono_iff_mono_app]
    intro n
    rw [mono_iff_injective]
    rintro ⟨a⟩ ⟨b⟩ h
    have hmono : Mono (g.app n) := ((NatTrans.mono_iff_mono_app g).mp ‹Mono g›) n
    have hab : a = b := (mono_iff_injective (g.app n)).mp hmono (congrArg ULift.down h)
    exact congrArg ULift.up hab
  let hp := uliftSSet_isPushout.{u, u + 1} (IsPushout.of_hasPushout f g)
  let G := hp.isoPushout.inv ≫ F
  have hA : Ind.HasPreservedColimit U (L.map f ≫ (pushout.inl (L.map f) (L.map g) ≫ G)) :=
    hcop (ULift.{u} ℕ × Fin 2) _
  have hB : Ind.HasPreservedColimit U (pushout.inl (L.map f) (L.map g) ≫ G) :=
    hcop (ULift.{u} ℕ) _
  have hC : Ind.HasPreservedColimit U (pushout.inr (L.map f) (L.map g) ≫ G) :=
    hasPreservedColimit_sequentialTelescopeIntervals U hcop _
  have hs : ∀ s : pointConeSpan.{u + 1} ⟶ X, Ind.HasPreservedColimit U s := by
    have : pointConeSpan.{u + 1}.Finite := SSet.finite_of_iso pointConeSpanIso.symm
    exact hfin _
  exact (Ind.hasPreservedColimit_iff_restrict_isIso U F hp.isoPushout.inv).mpr
    (Ind.hasPreservedColimit_pushout_shape U (L.map f) (L.map g) G hA hB hC hs)

end SerrePositivity.InfinityCategories.F2.Presentable
