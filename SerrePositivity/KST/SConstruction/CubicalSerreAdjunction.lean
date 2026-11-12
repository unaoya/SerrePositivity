module
public import SerrePositivity.KST.SConstruction.CubicalSerreChains

/-! # 元の cubical Serre 鎖の Yoneda 随伴と余極限保存
概要：元の左 Kan 延長を、制限 Yoneda の左随伴として回収する。
方針：元の Kan 単位を固定し、Yoneda 随伴の元の cell 上の評価を使う。
規約：元の鎖関手を置換しない。使われ方：Day tensor 比較の随伴による構成。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits Opposite Presheaf
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の鎖立方体からの射を集める、鎖複体の制限 Yoneda。 -/
def cubicalSerreRestrictedYoneda : Complex A ⥤ CubicalSet.{u} :=
  restrictedULiftYoneda.{u} (serreConcreteCubeComplexFunctor A)

/-- 元の cubical Serre 関手は元の Kan 単位の左 Kan 延長。 -/
instance cubicalSerreChains_isLeftKanExtension :
    (cubicalSerreChains A).IsLeftKanExtension (L := uliftYoneda.{u})
      (cubicalSerreChainsCubeUnit A) := by
  change (uliftYoneda.{u}.leftKanExtension (serreConcreteCubeComplexFunctor A)).IsLeftKanExtension
    (uliftYoneda.{u}.leftKanExtensionUnit (serreConcreteCubeComplexFunctor A))
  infer_instance

/-- 元の cubical Serre 鎖関手と制限 Yoneda の随伴。 -/
def cubicalSerreAdjunction : cubicalSerreChains A ⊣ cubicalSerreRestrictedYoneda A :=
  uliftYonedaAdjunction.{u} (cubicalSerreChains A) (cubicalSerreChainsCubeUnit A)

/-- 元の cubical Serre 鎖関手は任意のサイズの既存の余極限を保存する。 -/
instance cubicalSerreChains_preservesColimits :
    PreservesColimitsOfSize.{v, w} (cubicalSerreChains A) :=
  (cubicalSerreAdjunction A).leftAdjoint_preservesColimits

/-- 元の随伴の順方向は、元の各 cell への制限そのもの。 -/
lemma cubicalSerreAdjunction_homEquiv_cell {K : CubicalSet.{u}} {T : Complex A}
    (f : (cubicalSerreChains A).obj K ⟶ T) (c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) (x : K.obj (op c)) :
    (((cubicalSerreAdjunction A).homEquiv K T) f).app (op c) x =
      ULift.up (cubicalSerreCell A c x ≫ f) := by
  simp [cubicalSerreAdjunction, cubicalSerreRestrictedYoneda, uliftYonedaAdjunction,
    restrictedULiftYonedaHomEquiv, restrictedULiftYonedaHomEquiv',
    IsColimit.homEquiv, cubicalSerreCell, cubicalCell, Category.assoc]
  rfl

/-- 元の随伴の逆方向は、指定した全 cell の射を厳密に回収する。 -/
lemma cubicalSerreAdjunction_inverse_cell {K : CubicalSet.{u}} {T : Complex A}
    (a : K ⟶ (cubicalSerreRestrictedYoneda A).obj T)
    (c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) (x : K.obj (op c)) :
    cubicalSerreCell A c x ≫ ((cubicalSerreAdjunction A).homEquiv K T).symm a =
      (a.app (op c) x).down := by
  have h := cubicalSerreAdjunction_homEquiv_cell A
    (((cubicalSerreAdjunction A).homEquiv K T).symm a) c x
  rw [Equiv.apply_symm_apply] at h
  exact (congrArg ULift.down h).symm

end SerrePositivity.KST.SConstruction
