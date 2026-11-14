module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightPrism
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：left fibration の内部 Hom による保存。
方針：左ホーンと境界の積の pairing を任意の単射との pushout-product へ広げ、随伴で移す。
規約：モデル構造は使わず、左ホーンの持ち上げ性だけを扱う。
使われ方：Kerodon §5.3.1（Tag 035D）、left fibration の相対関手単体集合の Kan 性。

対応節は Kerodon 4.2（Tag 014H）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations

/-- 概要：左ホーンと任意の単射の pushout-product は left anodyne。
方針：内部 Hom の相対射の持ち上げ性を境界で検査し、積の pairing に帰着する。
規約：左ホーンの欠ける面は最後以外。
使われ方：Kerodon §4.2.5（Tag 0152）、§5.3.1（Tag 035D）、相対関手の左ホーン充填。 -/
lemma leftAnodyneExtensions_pushoutObjObj_horn {m : ℕ} (k : Fin (m + 1))
    {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (sq : (curriedTensor SSet.{u}).PushoutObjObj (horn (m + 1) k.castSucc).ι i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions sq.ι := by
  intro E D p hp
  let sq' := Functor.PullbackObjObj.ofHasPullback internalHom
    (horn (m + 1) k.castSucc).ι p
  rw [internalHomAdjunction₂.hasLiftingProperty_iff sq sq']
  suffices (monomorphisms SSet.{u}).rlp sq'.π from this _ inferInstance
  rw [SSet.rlp_monomorphisms]
  rintro _ _ _ ⟨n⟩
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff
    (Subcomplex.unionProd.pushoutObjObj.{u} (horn (m + 1) k.castSucc) (boundary n)) sq',
    Subcomplex.unionProd.pushoutObjObj_ι]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions_unionProd k n p hp

/-- 概要：左ホーンの包含と任意の単体集合の直積は left anodyne。
方針：空の単体集合からの包含との pushout-product を使う。
規約：パラメータ A の quasicategory 性は不要。
使われ方：Kerodon §5.3.1（Tag 035D）、内部 Hom の left fibration 性の随伴による証明。 -/
lemma leftAnodyneExtensions_horn_whiskerRight {m : ℕ} (k : Fin (m + 1))
    (A : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions ((horn (m + 1) k.castSucc).ι ▷ A) :=
  leftAnodyneExtensions_pushoutObjObj_horn k (initial.to A)
    (.ofIsInitialRight (curriedTensor _) (horn (m + 1) k.castSucc).ι
      (initial.to A) initialIsInitial)

/-- 概要：left fibration による後合成は任意の内部 Hom 上で left fibration。
方針：tensorRight と内部 Hom の随伴で、左ホーンとパラメータの積の持ち上げに移す。
規約：パラメータと底に quasicategory 性は要求しない。
使われ方：Kerodon §5.3.1（Tag 035D）、left fibration 上の関手の族の充填。 -/
@[kerodon 00TQ]
instance ihom_map_leftFibration {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (A : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration ((ihom A).map p) where
  mem := by
    intro K L i hi
    cases hi with
    | @intro n k hk =>
      obtain ⟨k, rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hk)
      exact (((ihom.adjunction A).ofNatIsoLeft
        (BraidedCategory.tensorLeftIsoTensorRight A)).hasLiftingProperty_iff _ p).1
        (leftAnodyneExtensions_horn_whiskerRight k A p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p)))

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "3.2.2.12" (partial := special) "仮定：p:X→S は Cartesian、q:Y→Z は cocartesian（Lean が強い：S=Δ⁰、q を left fibration に限定）。結論：この場合は Y′=Fun(X,Y),Z′=Fun(X,Z) と取れ、q′ が left、従って cocartesian fibration となる。全 Y と Y′ の辺が cocartesian なので (2) の辺の条件も両側が成立し一致。一般の相対 q には拡張しない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.ihom_map_leftFibration
