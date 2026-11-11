module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeBoundaryFamilySpace
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexPrismFirstVertex
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaces

/-!
概要：高次の面と底の図式が動く pointed transport の延長空間。
方針：面の包含と pointed-space 射影の相対内部 Hom を図式の族へ引き戻す。
規約：面・底・全パラメーターを厳密に保つ。
使われ方：straightening の三重以上の合成の境界固定の高次比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：高次の coherent な図式とその指定面の pointed な持ち上げの族。
方針：底を保つ射 p と面の包含 i を別々に保持する。
規約：定義段階では面の anodyne 性や p の充填性は要求しない。
使われ方：既に選んだ面を保つ高次 transport の入力。 -/
structure PointedTransportPrismFamily {A C E B K : SSet.{u + 1}}
    (i : C ⟶ A) (p : E ⟶ B) where
  diagram : (A ⊗ B) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}
  boundary : (C ⊗ E) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u}
  projection : boundary ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
    ((i ▷ E) ▷ K) ≫ ((A ◁ p) ▷ K) ≫ diagram

/-- 概要：面と pointed-space 射影の相対内部 Hom。
方針：係数 E を面の包含に掛けて標準引き戻しを取る。
規約：高次の面のパラメーター K はこの段階では外に置く。
使われ方：可変図式上の高次の持ち上げの空間。 -/
def pointedTransportPrismRelativeHom {A C : SSet.{u + 1}}
    (i : C ⟶ A) (E : SSet.{u + 1}) :
    internalHom.PullbackObjObj (i ▷ E) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection.{u} :=
  Functor.PullbackObjObj.ofHasPullback internalHom (i ▷ E) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection

/-- 概要：高次 transport の面と底の族を相対内部 Hom の底へ束ねる。
方針：二つの族を curry し射影条件で引き戻しへ持ち上げる。
規約：面も底の図式もパラメーター依存を許す。
使われ方：高次 lift 空間を定義する底の射。 -/
def PointedTransportPrismFamily.data {A C E B K : SSet.{u + 1}}
    {i : C ⟶ A} {p : E ⟶ B} (D : PointedTransportPrismFamily (K := K) i p) :
    K ⟶ (pointedTransportPrismRelativeHom i E).pt :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyData (i ▷ E) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
    (pointedTransportPrismRelativeHom i E) (curry D.boundary)
    (curry (((A ◁ p) ▷ K) ≫ D.diagram)) (by
      apply uncurry_injective
      rw [uncurry_natural_right, uncurry_curry, uncurry_pre_app, uncurry_curry]
      exact D.projection)

/-- 概要：指定された高次の面を延長する全 pointed transport の空間。
方針：相対内部 Hom の比較を指定データへ引き戻す。
規約：特定の延長を先に選ばない。
使われ方：高次の選択を族全体で比較する全空間。 -/
def PointedTransportPrismFamily.liftSpace {A C E B K : SSet.{u + 1}}
    {i : C ⟶ A} {p : E ⟶ B} (D : PointedTransportPrismFamily (K := K) i p) : SSet.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilySpace (pointedTransportPrismRelativeHom i E) D.data

/-- 概要：高次の持ち上げから元のパラメーターへ戻る射影。
方針：相対境界族の第二射影を取る。
規約：指定された面と底を同時に忘れず保持する。
使われ方：任意の部分パラメーター上の選択の延長。 -/
def PointedTransportPrismFamily.liftSpaceProjection {A C E B K : SSet.{u + 1}}
    {i : C ⟶ A} {p : E ⟶ B} (D : PointedTransportPrismFamily (K := K) i p) :
    D.liftSpace ⟶ K :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyProjection (pointedTransportPrismRelativeHom i E) D.data

/-- 概要：left anodyne な面の高次 transport の延長は全境界を持ち上げる。
方針：係数付き面の包含の相対内部 Hom の trivial Kan 性を底変換する。
規約：底・係数・パラメーターの小ささや充填性を仮定しない。
使われ方：任意の高次パラメーターの部分複体上の選択を保つ延長。 -/
lemma PointedTransportPrismFamily.liftSpaceProjection_trivialKanFibration
    {A C E B K : SSet.{u + 1}} {i : C ⟶ A} {p : E ⟶ B}
    (D : PointedTransportPrismFamily (K := K) i p) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration D.liftSpaceProjection := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.trivialKanFibration_relativeHom_of_leftAnodyne (i ▷ E)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftAnodyneExtensions_whiskerRight i hi E) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
    (pointedTransportPrismRelativeHom i E)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_pullback_snd _ _

/-- 概要：各パラメーターの固定面の高次 transport の延長の空間は可縮。
方針：実際の lift 射影の trivial Kan fibration の fiber を取る。
規約：頂点の存在や特定の延長を追加仮定にしない。
使われ方：高次の合成比較の選択空間の可縮性。 -/
lemma PointedTransportPrismFamily.liftSpaceFiber_isContractibleKan
    {A C E B K : SSet.{u + 1}} {i : C ⟶ A} {p : E ⟶ B}
    (D : PointedTransportPrismFamily (K := K) i p) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i)
    (k : K _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber D.liftSpaceProjection k) := by
  have := D.liftSpaceProjection_trivialKanFibration hi
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan _ _

/-- 概要：部分パラメーター上で選んだ高次の持ち上げを厳密に保って全体へ延長する。
方針：面と底を固定する相対内部 Hom の trivial Kan 射の持ち上げを uncurry する。
規約：面の包含は left anodyne、パラメーターの包含は任意の単射。
使われ方：低次の選択を変えずに高次の合成比較を構成する。 -/
lemma PointedTransportPrismFamily.exists_extension
    {A C E B K L : SSet.{u + 1}} {i : C ⟶ A} {p : E ⟶ B}
    (D : PointedTransportPrismFamily (K := K) i p) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i)
    (j : L ⟶ K) [Mono j] (W : (A ⊗ E) ⊗ L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u})
    (hWb : ((i ▷ E) ▷ L) ≫ W = ((C ⊗ E) ◁ j) ≫ D.boundary)
    (hWp : W ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
      ((A ⊗ E) ◁ j) ≫ ((A ◁ p) ▷ K) ≫ D.diagram) :
    ∃ U : (A ⊗ E) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u},
      ((A ⊗ E) ◁ j) ≫ U = W ∧
      ((i ▷ E) ▷ K) ≫ U = D.boundary ∧
      U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection = ((A ◁ p) ▷ K) ≫ D.diagram := by
  let r := pointedTransportPrismRelativeHom i E
  have hd₀ : D.data ≫ r.fst = curry D.boundary := by
    exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyData_fst _ _ _ _ _ _
  have hd₁ : D.data ≫ r.snd = curry (((A ◁ p) ▷ K) ≫ D.diagram) := by
    exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyData_snd _ _ _ _ _ _
  have hw : curry W ≫ r.π = j ≫ D.data := by
    apply r.hom_ext
    · rw [Category.assoc, r.π_fst, Category.assoc, hd₀]
      change curry W ≫ (pre (i ▷ E)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity = j ≫ curry D.boundary
      apply uncurry_injective
      rw [uncurry_pre_app, uncurry_curry, uncurry_natural_left, uncurry_curry]
      exact hWb
    · rw [Category.assoc, r.π_snd, Category.assoc, hd₁]
      change curry W ≫ (ihom (A ⊗ E)).map _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
        j ≫ curry (((A ◁ p) ▷ K) ≫ D.diagram)
      apply uncurry_injective
      rw [uncurry_natural_right, uncurry_curry, uncurry_natural_left, uncurry_curry]
      exact hWp
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.trivialKanFibration_relativeHom_of_leftAnodyne (i ▷ E)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftAnodyneExtensions_whiskerRight i hi E) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection r
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := r.π) j inferInstance
  let sq : CommSq (curry W) j r.π D.data := ⟨hw⟩
  have hb : sq.lift ≫ (pre (i ▷ E)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity = curry D.boundary := by
    calc
      _ = (sq.lift ≫ r.π) ≫ r.fst := by rw [Category.assoc, r.π_fst]; rfl
      _ = _ := by rw [sq.fac_right, hd₀]
  have hp : sq.lift ≫ (ihom (A ⊗ E)).map _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
      curry (((A ◁ p) ▷ K) ≫ D.diagram) := by
    calc
      _ = (sq.lift ≫ r.π) ≫ r.snd := by rw [Category.assoc, r.π_snd]; rfl
      _ = _ := by rw [sq.fac_right, hd₁]
  refine ⟨uncurry sq.lift, ?_, ?_, ?_⟩
  · rw [← uncurry_natural_left, sq.fac_left, uncurry_curry]
  · rw [← uncurry_pre_app, hb, uncurry_curry]
  · rw [← uncurry_natural_right, hp, uncurry_curry]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
