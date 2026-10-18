module

public import SerrePositivity.KST.DerivedGeometry.DGResolution.SupportTransport
public import Mathlib.CategoryTheory.Localization.LocalizerMorphism

/-!
# 分解前後の指定 Verdier 商の移送

概要：増大準同値による前三角化の同値を、指定 Verdier 商の同値へ降ろす。
方針：指定三角閉包の逆像の一致から trW の一致を証明し、既存の局所化を使う。
規約：冪等完備化を行わず、元の Hom の平坦性を追加しない。
使われ方：Drinfeld Thm 3.4・§3.5、KST D4、K-L1b・L3 の商の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v

namespace SerrePositivity.KST.DerivedGeometry.DGResolution

open CategoryTheory
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/--
概要：増大関手の前三角化への延長は圏同値。
方針：一般の準同値の前三角化比較を具体的な増大準同値へ適用する。
規約：分解後の元の Hom に追加条件は不要。
使われ方：Drinfeld Lemma 13.5・§3.5 の局所化の移送。
-/
instance augmentation_triaExtension_isEquivalence :
    (triaExtension A (Objects A D) D (augmentation A D)).IsEquivalence :=
  (triaEquivalence A (Objects A D) D (augmentation A D)
    (augmentation_quasiEquivalence A D)).isEquivalence_functor

/--
概要：増大関手で指定三角閉包の trW が正確に対応する。
方針：指定部分圏の逆像の一致と三角関手による cone の比較を使う。
規約：対象の一致だけで局所化の同値を済ませない。
使われ方：Drinfeld Thm 3.4・§3.5、KST D4 の Verdier 局所化。
-/
theorem augmentation_trW_eq (N : Set D) :
    (triaImage A (Objects A D) (nullObjects A D N)).trW =
      (triaImage A D N).trW.inverseImage (triaExtension A (Objects A D) D (augmentation A D)) := by
  have hP : triaImage A (Objects A D) (nullObjects A D N) =
      (triaImage A D N).inverseImage (triaExtension A (Objects A D) D (augmentation A D)) :=
    funext fun X => propext (augmentation_triaImage_iff A D N X).symm
  ext X Y f
  rw [hP, ObjectProperty.inverseImage_trW_iff]
  rfl

/--
概要：増大関手の前三角化比較を局所化の射として構成する。
方針：trW の逆像の一致を既存 LocalizerMorphism に渡す。
規約：弱同値の対応は証明済み。
使われ方：Drinfeld §3.5、KST D4 の商の移送の正方形。
-/
def verdierLocalizer (N : Set D) :
    LocalizerMorphism (triaImage A (Objects A D) (nullObjects A D N)).trW
      (triaImage A D N).trW := LocalizerMorphism.ofEq (augmentation_trW_eq A D N)

/--
概要：増大関手の局所化は同値になる。
方針：前三角化の圏同値と trW の逆像の一致から既存の局所化判定を使う。
規約：局所化の同値性を未証明の仮定にしない。
使われ方：Drinfeld §3.5、KST D4 の分解前後の商。
-/
instance verdierLocalizer_isLocalizedEquivalence (N : Set D) :
    (verdierLocalizer A D N).IsLocalizedEquivalence := by
  let : (verdierLocalizer A D N).functor.IsEquivalence :=
    augmentation_triaExtension_isEquivalence A D
  apply LocalizerMorphism.IsLocalizedEquivalence.of_equivalence
  change (triaImage A D N).trW ≤
    (triaImage A (Objects A D) (nullObjects A D N)).trW.map
      (triaExtension A (Objects A D) D (augmentation A D))
  rw [augmentation_trW_eq, MorphismProperty.map_inverseImage_eq_of_isEquivalence]

/--
概要：分解前後の指定 Verdier 商の圏同値。
方針：増大関手の前三角化比較の実際の局所化関手を用いる。
規約：完備化前の商を比較する。
使われ方：Drinfeld Thm 3.4・§3.5、KST D4 の係数つき局所化。
-/
def verdierEquivalence (N : Set D) :
    TriaQuotient A (Objects A D) (nullObjects A D N) ≌ TriaQuotient A D N :=
  ((verdierLocalizer A D N).localizedFunctor
    (triaQuotient A (Objects A D) (nullObjects A D N)) (triaQuotient A D N)).asEquivalence

/--
概要：分解前後の商の比較は、商を取る前の増大関手と可換な正方形を持つ。
方針：局所化の持ち上げの因子化同型を使う。
規約：元の三角関手と実際の商関手を保持する。
使われ方：Drinfeld §3.5、KST D4 の導来商と元の圏の比較。
-/
def verdierSquare (N : Set D) :
    triaQuotient A (Objects A D) (nullObjects A D N) ⋙ (verdierEquivalence A D N).functor ≅
      triaExtension A (Objects A D) D (augmentation A D) ⋙ triaQuotient A D N :=
  Localization.Lifting.iso _ (triaImage A (Objects A D) (nullObjects A D N)).trW
    ((verdierLocalizer A D N).functor ⋙ triaQuotient A D N)
    ((verdierLocalizer A D N).localizedFunctor
      (triaQuotient A (Objects A D) (nullObjects A D N)) (triaQuotient A D N))

/--
概要：分解前後の商の比較は指定局所化の持ち上げである。
方針：証明済みの可換正方形を登録する。
規約：実際の局所化関手を用いる。
使われ方：Drinfeld §3.5 の shift と三角形の移送。
-/
instance verdierEquivalenceLifting (N : Set D) :
    Localization.Lifting (triaQuotient A (Objects A D) (nullObjects A D N))
      (triaImage A (Objects A D) (nullObjects A D N)).trW
      (triaExtension A (Objects A D) D (augmentation A D) ⋙ triaQuotient A D N)
      (verdierEquivalence A D N).functor := ⟨verdierSquare A D N⟩

/--
概要：分解前後の商の順向き比較は shift と両立する。
方針：局所化を通して元の三角関手の shift を移送する。
規約：別の shift 構造は選ばない。
使われ方：Drinfeld §3.5 の三角比較。
-/
instance verdierEquivalenceFunctorCommShift (N : Set D) :
    (verdierEquivalence A D N).functor.CommShift ℤ :=
  Functor.commShiftOfLocalization (triaQuotient A (Objects A D) (nullObjects A D N))
    (triaImage A (Objects A D) (nullObjects A D N)).trW ℤ
    (triaExtension A (Objects A D) D (augmentation A D) ⋙ triaQuotient A D N)
    (verdierEquivalence A D N).functor

/--
概要：分解前後の商の逆向き比較は shift と両立する。
方針：同じ同値の順向きの shift 比較から構成する。
規約：随伴の整合性を保つ。
使われ方：Drinfeld §3.5 の三角同値。
-/
instance verdierEquivalenceInverseCommShift (N : Set D) :
    (verdierEquivalence A D N).inverse.CommShift ℤ :=
  (verdierEquivalence A D N).commShiftInverse ℤ

/--
概要：分解前後の商の随伴全体が shift と両立する。
方針：順関手の構造から単位・余単位に整合する構造を使う。
規約：同じ同値を維持する。
使われ方：Drinfeld §3.5 の三角同値。
-/
instance verdierEquivalenceCommShift (N : Set D) :
    (verdierEquivalence A D N).CommShift ℤ :=
  (verdierEquivalence A D N).commShift_of_functor ℤ

/--
概要：分解前後の商の可換正方形は shift 比較と両立する。
方針：局所化から移送した shift の因子化同型の整合性を使う。
規約：三角関手性の証明と同じ正方形を使う。
使われ方：Drinfeld §3.5、KST D4 の商の三角比較。
-/
instance verdierSquareCommShift (N : Set D) :
    NatTrans.CommShift (verdierSquare A D N).hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization
    (triaQuotient A (Objects A D) (nullObjects A D N))
    (triaImage A (Objects A D) (nullObjects A D N)).trW ℤ
    (triaExtension A (Objects A D) D (augmentation A D) ⋙ triaQuotient A D N)
    (verdierEquivalence A D N).functor

/--
概要：分解前後の商の順向き比較は区別三角形を保つ。
方針：局所化関手の射の本質的全射性で、商の前の可換正方形へ帰着する。
規約：三角関手性を追加仮定にしない。
使われ方：Drinfeld §3.5、KST D4 の Verdier 商の三角比較。
-/
instance verdierEquivalenceFunctorIsTriangulated (N : Set D) :
    (verdierEquivalence A D N).functor.IsTriangulated := by
  have : (triaQuotient A (Objects A D) (nullObjects A D N)).mapArrow.EssSurj :=
    Localization.essSurj_mapArrow _ (triaImage A (Objects A D) (nullObjects A D N)).trW
  exact Functor.isTriangulated_of_precomp_iso (verdierSquare A D N)

/--
概要：分解前後の指定 Verdier 商の同値は三角同値。
方針：shift の随伴整合性と順向きの三角関手性をまとめる。
規約：冪等完備化はしない。
使われ方：Drinfeld §3.5、KST D4 の分解の移送。
-/
instance verdierEquivalenceIsTriangulated (N : Set D) :
    (verdierEquivalence A D N).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _ (verdierEquivalenceFunctorIsTriangulated A D N)

/--
概要：分解後の path 商の前三角化は元の指定 Verdier 商と同値。
方針：平坦な path 商の比較と、増大関手による商の移送を合成する。
規約：元の Hom の平坦性と冪等完備化を追加しない。
使われ方：Drinfeld Thm 3.4・§3.5、KST D4、K-L1b・L3 の商への供給。
-/
def quotientToOriginalVerdierEquivalence (N : Set D) :
    TriaCategory A (Quotient A D N) ≌ TriaQuotient A D N :=
  (quotientTriaEquivalence A D N).symm.trans (verdierEquivalence A D N)

/--
概要：path 商から元の商への比較の順関手は shift と両立する。
方針：二つの比較の shift 構造を合成する。
規約：平坦性は分解側で証明済み。
使われ方：Drinfeld Thm 3.4・§3.5 の合成比較。
-/
instance quotientToOriginalVerdierFunctorCommShift (N : Set D) :
    (quotientToOriginalVerdierEquivalence A D N).functor.CommShift ℤ := by
  dsimp [quotientToOriginalVerdierEquivalence]
  infer_instance

/--
概要：path 商から元の商への比較の逆関手は shift と両立する。
方針：同じ合成同値の構造を維持する。
規約：shift 比較を選び直さない。
使われ方：Drinfeld Thm 3.4・§3.5 の合成比較。
-/
instance quotientToOriginalVerdierInverseCommShift (N : Set D) :
    (quotientToOriginalVerdierEquivalence A D N).inverse.CommShift ℤ := by
  dsimp [quotientToOriginalVerdierEquivalence]
  infer_instance

/--
概要：path 商から元の商への比較の随伴は shift と両立する。
方針：三角同値の合成の構造を使う。
規約：完備化前の商を使う。
使われ方：Drinfeld Thm 3.4・§3.5 の合成比較。
-/
instance quotientToOriginalVerdierCommShift (N : Set D) :
    (quotientToOriginalVerdierEquivalence A D N).CommShift ℤ := by
  dsimp [quotientToOriginalVerdierEquivalence]
  infer_instance

/--
概要：分解後の path 商の前三角化と元の指定 Verdier 商は三角同値。
方針：平坦な商比較と増大準同値による三角同値を合成する。
規約：元の Hom の平坦性を仮定せず、完備化もしない。
使われ方：Drinfeld Thm 3.4・§3.5、KST D4、K-L1b・L3 の商。
-/
instance quotientToOriginalVerdierIsTriangulated (N : Set D) :
    (quotientToOriginalVerdierEquivalence A D N).IsTriangulated := by
  dsimp [quotientToOriginalVerdierEquivalence]
  infer_instance

end SerrePositivity.KST.DerivedGeometry.DGResolution
