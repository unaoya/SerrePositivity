module

public import SerrePositivity.InfinityCategories.F2.Presentable.TensorAdjunctionUnit

/-!
概要：元の二つの全随伴から、直積の全随伴を構成する。
方針：元の直積単位の全 Hom 比較を成分ごとの全単射と同定する。
規約：単位・余単位と両三角式を持つ随伴を返し、随伴関手定理は使わない。
使われ方：presentable 圏の積の反映模型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

variable {X Y X' Y' : SSet.{u}} [Quasicategory X] [Quasicategory Y]
  [Quasicategory X'] [Quasicategory Y']
  {F : X ⟶ Y} {R : Y ⟶ X} {G : X' ⟶ Y'} {S : Y' ⟶ X'}

local instance : Quasicategory (X ⊗ X') := F2.quasicategory_tensor X X'
local instance : Quasicategory (Y ⊗ Y') := F2.quasicategory_tensor Y Y'

/-- 概要：直積の元の二関手は全随伴をなす。
方針：構成した元の直積単位の各パラメーター Hom 比較を二成分の全単射へ分解する。
規約：余単位や三角恒等式は構成し、入力に置かない。
使われ方：反映像の直積の生成対象を構成する。 -/
def tensorAdjunction (a : QCatAdjunction F R) (b : QCatAdjunction G S) :
    QCatAdjunction (F ⊗ₘ G) (R ⊗ₘ S) := by
  apply qcatAdjunctionOfUnitHomBijective (tensorAdjunctionUnit a b)
  intro A hA U V
  let p := functorHomTensorEquiv (U ≫ (F ⊗ₘ G)) V
  let q := functorHomTensorEquiv U (V ≫ (R ⊗ₘ S))
  let e : FunctorHom (U ≫ (F ⊗ₘ G)) V ≃ FunctorHom U (V ≫ (R ⊗ₘ S)) :=
    p.trans (((a.homEquiv (U ≫ fst X X') (V ≫ fst Y Y')).prodCongr
      (b.homEquiv (U ≫ snd X X') (V ≫ snd Y Y'))).trans q.symm)
  have he : qcatUnitHomMap (tensorAdjunctionUnit a b) U V = e := by
    funext α
    apply q.injective
    have h := q.apply_symm_apply
      (((a.homEquiv (U ≫ fst X X') (V ≫ fst Y Y')).prodCongr
        (b.homEquiv (U ≫ snd X X') (V ≫ snd Y Y'))) (p α))
    exact (tensorAdjunctionUnit_homMap_components a b U V α).trans h.symm
  rw [he]
  exact e.bijective

end SerrePositivity.InfinityCategories.F2.Presentable
