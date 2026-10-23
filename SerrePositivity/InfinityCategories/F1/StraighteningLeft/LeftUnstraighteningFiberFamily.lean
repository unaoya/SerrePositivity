module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningFiberTransport
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningMappingSpaceMap
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorFiberHom

/-!
概要：写像空間比較射全体の fiber での作用を、pointed space への一つの持ち上げの族で表示する。
方針：普遍的な変換の持ち上げの始域を fiber へ制限し、相対写像空間の fiber への作用を評価する。
規約：変換の空間全体がパラメーターであり、頂点ごとの選択を追加しない。
使われ方：Kerodon Corollary 5.6.0.6、選択済み比較射と空間値の写像空間の比較の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：写像空間比較射を pointed-space の fiber 間の関手空間へ制限する。
方針：相対 Hom の fiber への作用の両側を引き戻しの fiber 同型で移送する。
規約：追加パラメーターは元の変換の空間全体。
使われ方：Kerodon Corollary 5.6.0.6、比較射の値での作用を全次数で表す射。 -/
noncomputable def leftUnstraighteningMappingFiberHom {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌) :
    leftUnstraighteningTransformationSpace F G ⟶
      (ihom (vertexFiber pointedSpaceProjection (F.app _ b))).obj
        (vertexFiber pointedSpaceProjection (G.app _ b)) :=
  leftUnstraighteningMappingSpaceMap F G ≫
    relativeFunctorFiberHom (leftUnstraighteningProjection F) (leftUnstraighteningProjection G) b ≫
    (pre (leftUnstraighteningFiberIso F b).inv).app
      (vertexFiber (leftUnstraighteningProjection G) b) ≫
    (ihom (vertexFiber pointedSpaceProjection (F.app _ b))).map
      (leftUnstraighteningFiberIso G b).hom

/-- 概要：普遍的な変換の持ち上げを pointed-space の始域 fiber 全体へ制限する。
方針：始域の fiber 同型の逆と fiber の包含を prism の始域に適用する。
規約：既存の普遍的な持ち上げの選択をそのまま使う。
使われ方：Kerodon Corollary 5.6.0.6、fiber 間の関手空間への比較の持ち上げの証人。 -/
noncomputable def leftUnstraighteningFiberFamilyLift {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌) :
    ((Δ[1] : SSet.{u + 1}) ⊗ vertexFiber pointedSpaceProjection (F.app _ b)) ⊗
      leftUnstraighteningTransformationSpace F G ⟶ PointedSpaceInfinity.{u} :=
  ((Δ[1] ◁ ((leftUnstraighteningFiberIso F b).inv ≫
    vertexFiberι (leftUnstraighteningProjection F) b)) ▷
      leftUnstraighteningTransformationSpace F G) ≫ leftUnstraighteningTransformationFamilyLift F G

/-- 概要：fiber に制限した持ち上げの始点は元の pointed-space fiber の包含に定値。
方針：パラメーター付き prism の頂点の自然性と fiber 同型の往復を使う。
規約：初期値は変換の空間全体で固定する。
使われ方：Kerodon Corollary 5.6.0.6、fiber 上のパラメーター付き transport の初期条件。 -/
lemma leftUnstraighteningFiberFamilyLift_start {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌) :
    (simplexPrismVertex 1 0 (vertexFiber pointedSpaceProjection (F.app _ b)) ▷
      leftUnstraighteningTransformationSpace F G) ≫ leftUnstraighteningFiberFamilyLift F G b =
    fst _ _ ≫ vertexFiberι pointedSpaceProjection (F.app _ b) := by
  rw [leftUnstraighteningFiberFamilyLift, ← Category.assoc,
    simplexPrismVertex_parameterizedBaseChange, leftUnstraighteningTransformationFamilyLift_start,
    whiskerRight_fst_assoc]
  exact congrArg (fun z ↦ fst _ (leftUnstraighteningTransformationSpace F G) ≫ z)
    (leftUnstraighteningFiberIso_inv_ι_fst F b)

/-- 概要：fiber に制限した持ち上げは、普遍的な変換を b で評価した区間の族を被覆する。
方針：始域の射影が b に定値なことと、パラメーター付き prism の定値制限公式を使う。
規約：変換の空間の全高次単体を保持する。
使われ方：Kerodon Corollary 5.6.0.6、fiber 上のパラメーター付き transport の底の条件。 -/
lemma leftUnstraighteningFiberFamilyLift_projection {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌) :
    leftUnstraighteningFiberFamilyLift F G b ≫ pointedSpaceProjection =
    (fst (Δ[1] : SSet.{u + 1}) (vertexFiber pointedSpaceProjection (F.app _ b)) ▷
      leftUnstraighteningTransformationSpace F G) ≫
      intervalMappingUncurry (𝟙 (leftUnstraighteningTransformationSpace F G)) ≫
        evaluateFunctorAt b := by
  have hi : ((leftUnstraighteningFiberIso F b).inv ≫
      vertexFiberι (leftUnstraighteningProjection F) b) ≫ leftUnstraighteningProjection F =
        SSet.const b := by
    rw [Category.assoc, vertexFiberι_comp, SSet.comp_const]
  rw [leftUnstraighteningFiberFamilyLift, Category.assoc,
    leftUnstraighteningTransformationFamilyLift_projection, ← Category.assoc,
    ← comp_whiskerRight, ← MonoidalCategory.whiskerLeft_comp, hi,
    leftUnstraighteningTransformationFamily, functorParameterizedPrism_const]

/-- 概要：fiber 間の写像空間の作用の評価は、元の比較射の評価の fiber への制限。
方針：前合成・後合成の uncurry の自然性と fiber の包含の計算則を使う。
規約：変換の空間全体に対する等式。
使われ方：Kerodon Corollary 5.6.0.6、写像空間への作用と普遍的な持ち上げの終点の接続。 -/
lemma leftUnstraighteningMappingFiberHom_uncurry {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌) :
    uncurry (leftUnstraighteningMappingFiberHom F G b) ≫
      vertexFiberι pointedSpaceProjection (G.app _ b) =
    (((leftUnstraighteningFiberIso F b).inv ≫
      vertexFiberι (leftUnstraighteningProjection F) b) ▷
        leftUnstraighteningTransformationSpace F G) ≫
      relativeFunctorUncurry (leftUnstraighteningMappingSpaceMap F G) ≫
        pullback.fst pointedSpaceProjection G := by
  rw [leftUnstraighteningMappingFiberHom, ← Category.assoc, ← Category.assoc,
    uncurry_natural_right, uncurry_pre_app, Category.assoc, Category.assoc,
    leftUnstraighteningFiberIso_hom_ι]
  have h := relativeFunctorFiberHom_uncurry (leftUnstraighteningProjection F)
    (leftUnstraighteningProjection G) b (leftUnstraighteningMappingSpaceMap F G)
  exact congrArg (fun z ↦ ((leftUnstraighteningFiberIso F b).inv ▷
    leftUnstraighteningTransformationSpace F G) ≫ z ≫ pullback.fst pointedSpaceProjection G) h

/-- 概要：写像空間比較射の fiber での作用を評価すると、fiber に制限した普遍的な持ち上げの終点になる。
方針：比較射の pointed space 成分の式と、prism の頂点の自然性を使う。
規約：零単体だけでなく全ての変換の高次の族を同時に比較する。
使われ方：Kerodon Corollary 5.6.0.6、選択済み比較射の全次数の作用を transport の族へ移す。 -/
lemma leftUnstraighteningFiberFamilyLift_end {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌) :
    uncurry (leftUnstraighteningMappingFiberHom F G b) ≫
      vertexFiberι pointedSpaceProjection (G.app _ b) =
    (simplexPrismVertex 1 1 (vertexFiber pointedSpaceProjection (F.app _ b)) ▷
      leftUnstraighteningTransformationSpace F G) ≫ leftUnstraighteningFiberFamilyLift F G b := by
  rw [leftUnstraighteningMappingFiberHom_uncurry, leftUnstraighteningFiberFamilyLift]
  conv_rhs => rw [← Category.assoc, simplexPrismVertex_parameterizedBaseChange]
  exact congrArg (fun z ↦ (((leftUnstraighteningFiberIso F b).inv ≫
    vertexFiberι (leftUnstraighteningProjection F) b) ▷
      leftUnstraighteningTransformationSpace F G) ≫ z)
    (leftUnstraighteningMappingSpaceMap_pointed F G)

end SerrePositivity.InfinityCategories
