module
public import SerrePositivity.InfinityCategories.Stable.LeftFibrationTransportHom
public import SerrePositivity.InfinityCategories.F1.CoconeMappingPiZero
public import SerrePositivity.InfinityCategories.F1.CoconeMappingRestriction

/-! # 余錐空間の終点輸送と Hom の後合成

概要：終点の辺に沿って余錐空間を輸送でき、余極限の Hom 表示で後合成になる。
方針：coslice 射影の left fibration 性を用い、単射の図式制限に沿って輸送を持ち上げる。
規約：輸送は実際の区間族を含む。使われ方：二枝のループ積の Hom 上の自然性への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：任意の終点の辺に沿う余錐空間全体の輸送が存在する。
方針：coslice 射影の left fibration に一般の fiber 輸送を適用する。
規約：図式の余極限性は不要、X は quasicategory。使われ方：共通始点の余錐の輸送を選ぶ。 -/
lemma nonempty_coconeEndpointTransport {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) {x y : X _⦋0⦌}
    (a : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) :
    Nonempty (LeftFibrationFiberTransport (sliceUnderProjection p) a) :=
  nonempty_leftFibrationFiberTransport (sliceUnderProjection p) a

/-- 概要：余錐空間の終点輸送は余極限頂点からの Hom 表示で後合成となる。
方針：coslice の始対象としての余極限性と一般の fiber 輸送の Hom 公式を使う。
規約：任意の選んだ輸送について成立。使われ方：ループ演算を Hom に移す際の終点自然性。 -/
lemma coconeMappingSpacePiZeroEquiv_transport {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c : JoinCocone p) (hc : IsColimitCone c) {x y : X _⦋0⦌}
    (a : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (T : LeftFibrationFiberTransport (sliceUnderProjection p) a)
    (b : SSet.π₀ (coconeMappingSpace p x)) :
    coconeMappingSpacePiZeroEquiv c hc y (SSet.mapπ₀ T.map b) =
      coconeMappingSpacePiZeroEquiv c hc x b ≫ SSet.Truncated.HomotopyCategory.homMk a :=
  leftFibrationInitialFiberPiZeroEquiv_transport (sliceUnderProjection p) c hc a T b

/-- 概要：部分図式の余錐の輸送を、単射の図式制限と厳密に可換な全図式の輸送へ持ち上げられる。
方針：coslice 制限の left fibration 性を使い、区間族そのものを持ち上げる。
規約：先に選んだ部分図式の輸送は変更しない。使われ方：同じ枝を二度使う span の同時輸送。 -/
lemma exists_coconeEndpointTransport_restrict {K L X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (i : L ⟶ K) [Mono i] {x y : X _⦋0⦌}
    (a : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (T : LeftFibrationFiberTransport (sliceUnderProjection (i ≫ p)) a) :
    ∃ S : LeftFibrationFiberTransport (sliceUnderProjection p) a,
      S.h ≫ sliceUnderRestrict p i = (cosliceRestrictionFiberMap p i x ▷ (Δ[1] : SSet.{u})) ≫ T.h ∧
      S.map ≫ cosliceRestrictionFiberMap p i y = cosliceRestrictionFiberMap p i x ≫ T.map := by
  have := sliceUnderRestrict_leftFibration_of_mono p i
  exact exists_leftFibrationFiberTransport_lift (sliceUnderProjection p)
    (sliceUnderProjection (i ≫ p)) (sliceUnderRestrict p i)
    (sliceUnderRestrict_projection p i) a T

end SerrePositivity.InfinityCategories
