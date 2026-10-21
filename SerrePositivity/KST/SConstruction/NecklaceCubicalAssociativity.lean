module
public import SerrePositivity.KST.SConstruction.CubicalCompositionTensorCalculus
public import SerrePositivity.KST.SConstruction.NecklaceCubicalTripleExt
public import SerrePositivity.KST.SConstruction.NecklaceInStructuralIso

/-! # 元の cubical mapping object の合成の結合則
概要：元の全 mapping object 上の Day tensor 合成は、元の結合同型と両立する。
方針：三つの全生成射で判定し、元の強モノイダル比較と K 内の結合同型を照合する。
規約：元の全高次単体と生成射を保持。使われ方：cubical rigidification の豊穣圏構造。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Simplicial SSet

/-- 元の三つの生成射で、左右の結合の合成は元の Day 結合同型と一致する。 -/
lemma necklaceCubicalDay_assoc_cell {K : SSet.{u}} {w x y z : K _⦋0⦌}
    (T : NecklaceIn K w x) (U : NecklaceIn K x y) (V : NecklaceIn K y z) :
    ((necklaceCubicalDayCell T ⊗ₘ necklaceCubicalDayCell U) ⊗ₘ
        necklaceCubicalDayCell V) ≫
        necklaceCubicalDayCompose K w x y ▷ necklaceCubicalDayMapping K y z ≫
        necklaceCubicalDayCompose K w y z =
      (α_ (necklaceCubicalDay.obj T.necklace) (necklaceCubicalDay.obj U.necklace)
        (necklaceCubicalDay.obj V.necklace)).hom ≫
        (necklaceCubicalDayCell T ⊗ₘ
          (necklaceCubicalDayCell U ⊗ₘ necklaceCubicalDayCell V)) ≫
        necklaceCubicalDayMapping K w x ◁ necklaceCubicalDayCompose K x y z ≫
        necklaceCubicalDayCompose K w x z := by
  have hl := cubicalComposeTensor_left
    (necklaceCubicalDayCell T) (necklaceCubicalDayCell U) (necklaceCubicalDayCell V)
    (necklaceCubicalDayCompose K w x y) (necklaceCubicalDayCompose K w y z)
    (Functor.LaxMonoidal.μ necklaceCubicalDay T.necklace U.necklace)
    (necklaceCubicalDayCell (necklaceInWedge T U))
    (Functor.LaxMonoidal.μ necklaceCubicalDay
      (necklaceWedge T.necklace U.necklace) V.necklace)
    (necklaceCubicalDayCell (necklaceInWedge (necklaceInWedge T U) V))
    (necklaceCubicalDayCompose_cell T U)
    (necklaceCubicalDayCompose_cell (necklaceInWedge T U) V)
  have hr := cubicalComposeTensor_right
    (necklaceCubicalDayCell T) (necklaceCubicalDayCell U) (necklaceCubicalDayCell V)
    (necklaceCubicalDayCompose K x y z) (necklaceCubicalDayCompose K w x z)
    (Functor.LaxMonoidal.μ necklaceCubicalDay U.necklace V.necklace)
    (necklaceCubicalDayCell (necklaceInWedge U V))
    (Functor.LaxMonoidal.μ necklaceCubicalDay T.necklace
      (necklaceWedge U.necklace V.necklace))
    (necklaceCubicalDayCell (necklaceInWedge T (necklaceInWedge U V)))
    (necklaceCubicalDayCompose_cell U V)
    (necklaceCubicalDayCompose_cell T (necklaceInWedge U V))
  have hc : necklaceCubicalDay.map (α_ T.necklace U.necklace V.necklace).hom ≫
      necklaceCubicalDayCell (necklaceInWedge T (necklaceInWedge U V)) =
      necklaceCubicalDayCell (necklaceInWedge (necklaceInWedge T U) V) :=
    necklaceCubicalDayCell_relation (necklaceInAssociator T U V).hom
  have hm := congrArg (fun b =>
    (Functor.LaxMonoidal.μ necklaceCubicalDay T.necklace U.necklace ▷
      necklaceCubicalDay.obj V.necklace) ≫
      Functor.LaxMonoidal.μ necklaceCubicalDay
        (necklaceWedge T.necklace U.necklace) V.necklace ≫ b) hc.symm
  have hmid :
      (Functor.LaxMonoidal.μ necklaceCubicalDay T.necklace U.necklace ▷
        necklaceCubicalDay.obj V.necklace) ≫
        Functor.LaxMonoidal.μ necklaceCubicalDay
          (necklaceWedge T.necklace U.necklace) V.necklace ≫
        necklaceCubicalDayCell (necklaceInWedge (necklaceInWedge T U) V) =
      (α_ (necklaceCubicalDay.obj T.necklace) (necklaceCubicalDay.obj U.necklace)
        (necklaceCubicalDay.obj V.necklace)).hom ≫
        necklaceCubicalDay.obj T.necklace ◁
          Functor.LaxMonoidal.μ necklaceCubicalDay U.necklace V.necklace ≫
        Functor.LaxMonoidal.μ necklaceCubicalDay T.necklace
          (necklaceWedge U.necklace V.necklace) ≫
        necklaceCubicalDayCell (necklaceInWedge T (necklaceInWedge U V)) := by
    exact hm.trans (cubicalComposeTensor_postcompose_eq _ _ _ _ _ _ _
      (Functor.LaxMonoidal.associativity necklaceCubicalDay
        T.necklace U.necklace V.necklace))
  exact hl.trans (hmid.trans
    ((congrArg (fun b =>
      (α_ (necklaceCubicalDay.obj T.necklace) (necklaceCubicalDay.obj U.necklace)
        (necklaceCubicalDay.obj V.necklace)).hom ≫ b) hr).symm))

/-- 元の全 mapping object の合成は、元の Day tensor の結合同型と両立する。 -/
lemma necklaceCubicalDay_assoc (K : SSet.{u}) (w x y z : K _⦋0⦌) :
    necklaceCubicalDayCompose K w x y ▷ necklaceCubicalDayMapping K y z ≫
        necklaceCubicalDayCompose K w y z =
      (α_ (necklaceCubicalDayMapping K w x) (necklaceCubicalDayMapping K x y)
        (necklaceCubicalDayMapping K y z)).hom ≫
        necklaceCubicalDayMapping K w x ◁ necklaceCubicalDayCompose K x y z ≫
        necklaceCubicalDayCompose K w x z := by
  apply necklaceCubicalDayTriple_hom_ext K w x y z
  intro T U V
  have hn := associator_naturality (necklaceCubicalDayCell T)
    (necklaceCubicalDayCell U) (necklaceCubicalDayCell V)
  have hl := necklaceCubicalDay_assoc_cell T U V
  exact hl.trans ((congrArg (fun b => b ≫
    necklaceCubicalDayMapping K w x ◁ necklaceCubicalDayCompose K x y z ≫
      necklaceCubicalDayCompose K w x z) hn).trans (Category.assoc _ _ _)).symm

end SerrePositivity.KST.SConstruction
