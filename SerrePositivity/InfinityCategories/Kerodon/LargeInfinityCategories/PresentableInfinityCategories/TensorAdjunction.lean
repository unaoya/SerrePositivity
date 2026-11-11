module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.TensorAdjunctionUnit

/-!
概要：元の二つの全随伴から、直積の全随伴を構成する。
方針：元の直積単位の全 Hom 比較を成分ごとの全単射と同定する。
規約：単位・余単位と両三角式を持つ随伴を返し、随伴関手定理は使わない。
使われ方：presentable 圏の積の反映模型。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {X Y X' Y' : SSet.{u}} [Quasicategory X] [Quasicategory Y]
  [Quasicategory X'] [Quasicategory Y']
  {F : X ⟶ Y} {R : Y ⟶ X} {G : X' ⟶ Y'} {S : Y' ⟶ X'}

local instance : Quasicategory (X ⊗ X') := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategory_tensor X X'
local instance : Quasicategory (Y ⊗ Y') := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategory_tensor Y Y'

/-- 概要：直積の元の二関手は全随伴をなす。
方針：構成した元の直積単位の各パラメーター Hom 比較を二成分の全単射へ分解する。
規約：余単位や三角恒等式は構成し、入力に置かない。
使われ方：反映像の直積の生成対象を構成する。 -/
def tensorAdjunction (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F R) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction G S) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (F ⊗ₘ G) (R ⊗ₘ S) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatAdjunctionOfUnitHomBijective (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.tensorAdjunctionUnit a b)
  intro A hA U V
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomTensorEquiv (U ≫ (F ⊗ₘ G)) V
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomTensorEquiv U (V ≫ (R ⊗ₘ S))
  let e : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (U ≫ (F ⊗ₘ G)) V ≃ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U (V ≫ (R ⊗ₘ S)) :=
    p.trans (((a.homEquiv (U ≫ fst X X') (V ≫ fst Y Y')).prodCongr
      (b.homEquiv (U ≫ snd X X') (V ≫ snd Y Y'))).trans q.symm)
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.tensorAdjunctionUnit a b) U V = e := by
    funext α
    apply q.injective
    have h := q.apply_symm_apply
      (((a.homEquiv (U ≫ fst X X') (V ≫ fst Y Y')).prodCongr
        (b.homEquiv (U ≫ snd X X') (V ≫ snd Y Y'))) (p α))
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.tensorAdjunctionUnit_homMap_components a b U V α).trans h.symm
  rw [he]
  exact e.bijective

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
