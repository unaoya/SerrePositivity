module

public import SerrePositivity.InfinityCategories.HTT.RetractsAndIdempotentCompletion.RetractClosure
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Walking
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：coherent な冪等図式と、元の全図式を制限で回収する強い分裂。
方針：全 nerve 上の単体的写像を使用し、元の三角形からホモトピー圏の retract を回収する。
規約：一つの冪等な射の類だけを coherent 図式とは扱わない。
使われ方：HTT 4.4.5 の分裂と、前層の retract 閉包との接続。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 通常の圏の射を、元の nerve の同じ辺のホモトピー類に送る関手。 -/
def nerveHomotopyFunctor (C : Type u) [SmallCategory C] : C ⥤ hoFunctor.obj (nerve C) where
  obj x := HomotopyCategory.mk (nerveEquiv.symm x)
  map f := HomotopyCategory.homMk (nerve.edgeMk f)
  map_id x := by
    rw [nerve.edgeMk_id, HomotopyCategory.homMk_id]
  map_comp f g := by
    obtain ⟨h⟩ := (nerve.nonempty_compStruct_iff f g (f ≫ g)).mpr rfl
    exact (HomotopyCategory.homMk_comp_homMk h).symm

/-- 元の全 Idem 上の写像としての coherent 冪等図式。 -/
@[kerodon 03ZT]
abbrev CoherentIdempotent (X : SSet.{u}) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IdemShape.{u} ⟶ X

/-- 元の全冪等図式を同じ包含の制限で厳密に回収する強い分裂。 -/
@[kerodon 03ZX]
def StrongSplitting {X : SSet.{u}} (d : CoherentIdempotent X) :=
  {s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplitShape.{u} ⟶ X // _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusion ≫ s = d}

/-- 任意の coherent 冪等図式の強い分裂の存在による冪等完備性。 -/
@[kerodon 0406]
def IsIdempotentComplete (X : SSet.{u}) : Prop :=
  ∀ d : CoherentIdempotent X, Nonempty (StrongSplitting d)

/-- 元の強い分裂を、同じ図式とともに後合成する。 -/
def StrongSplitting.map {X Y : SSet.{u}} {d : CoherentIdempotent X}
    (s : StrongSplitting d) (F : X ⟶ Y) : StrongSplitting (d ≫ F) :=
  ⟨s.val ≫ F, by rw [← Category.assoc, s.property]⟩

/-- coherent 冪等図式の元の対象。 -/
def CoherentIdempotent.vertex {X : SSet.{u}} (d : CoherentIdempotent X) : X _⦋0⦌ :=
  d.app (Opposite.op ⦋0⦌) (nerveEquiv.symm _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingObject)

/-- 元の coherent 冪等図式が指定する、同じ対象のホモトピー圏内の射。 -/
def CoherentIdempotent.endomorphism {X : SSet.{u}} (d : CoherentIdempotent X) :
    HomotopyCategory.mk d.vertex ⟶ HomotopyCategory.mk d.vertex :=
  ((nerveHomotopyFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingIdem.{u}) ⋙ (hoFunctor.map d).toFunctor).map _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingIdempotent

/-- 元の全 coherent 図式から得た同じ射は、元の冪等関係を満たす。 -/
lemma CoherentIdempotent.endomorphism_idem {X : SSet.{u}} (d : CoherentIdempotent X) :
    d.endomorphism ≫ d.endomorphism = d.endomorphism := by
  exact (Functor.map_comp
    ((nerveHomotopyFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingIdem.{u}) ⋙ (hoFunctor.map d).toFunctor)
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingIdempotent _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingIdempotent).symm.trans
      (congrArg
        (((nerveHomotopyFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingIdem.{u}) ⋙ (hoFunctor.map d).toFunctor).map)
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingIdempotent_idem)

/-- 同じ強い分裂の元の分裂対象。 -/
def StrongSplitting.vertex {X : SSet.{u}} {d : CoherentIdempotent X}
    (s : StrongSplitting d) : X _⦋0⦌ :=
  s.val.app (Opposite.op ⦋0⦌) (nerveEquiv.symm _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage)

/-- 強い分裂の元の非分裂対象は、同じ元の冪等図式の対象そのもの。 -/
lemma StrongSplitting.source_eq {X : SSet.{u}} {d : CoherentIdempotent X}
    (s : StrongSplitting d) :
    s.val.app (Opposite.op ⦋0⦌) (nerveEquiv.symm _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource) = d.vertex := by
  have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) (nerveEquiv.symm _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingObject))
    s.property
  exact h

/-- 元の強い分裂は、同じ二頂点のホモトピー圏内の元の retract を与える。 -/
def StrongSplitting.vertexRetraction {X : SSet.{u}} {d : CoherentIdempotent X}
    (s : StrongSplitting d) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction s.vertex d.vertex := by
  let r : Retract _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource.{u} :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSection, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingRetraction, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSection_retraction⟩
  have t := (r.map (nerveHomotopyFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit.{u})).map
    (hoFunctor.map s.val).toFunctor
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction s.vertex
    (s.val.app (Opposite.op ⦋0⦌) (nerveEquiv.symm _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource)) at t
  rw [s.source_eq] at t
  exact t

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
