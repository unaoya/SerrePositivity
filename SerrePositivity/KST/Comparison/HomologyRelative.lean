module

public import SerrePositivity.KST.Comparison.HomologyDegenerate
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# 相対整数ホモロジー

概要：正規化鎖写像の余核から相対整数ホモロジーを構成する。
方針：可換正方形から余核の鎖写像を作り、単射の場合は実際の短完全列を使う。
規約：Weibel K-book III、Waldhausen LNM 1126 §1.7・§1.8。一般の写像の余核とホモトピー余ファイバーは区別する。
使われ方：セル添付の相対ホモロジーと plus のホモロジー比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial

/--
概要：単射な単体写像の非正規化整数鎖写像は単射である。
方針：自由アーベル群関手の単射保存を各次数に適用する。
規約：単射性は単体集合の圏のモノ射で表す。
使われ方：包含に対する相対複体の短完全性。
-/
instance unnormalizedIntegralChains_map_mono {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] :
    Mono (unnormalizedIntegralChains.map f) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  change Mono (AddCommGrpCat.free.map (f.app (Opposite.op ⦋n⦌)))
  have : Mono (f.app (Opposite.op ⦋n⦌)) :=
    (NatTrans.mono_iff_mono_app f).mp inferInstance _
  exact AddCommGrpCat.free.map_mono _

/--
概要：単射な単体写像の正規化整数鎖写像は単射である。
方針：正規化包含の自然性と、非正規化鎖写像の単射性を使う。
規約：単射性を追加の仮定とせず元の単体写像から導く。
使われ方：部分単体集合との相対ホモロジーの長完全列。
-/
instance normalizedIntegralChains_map_mono {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] :
    Mono (normalizedIntegralChains.map f) := by
  have (Z : SSet.{u}) : Mono (normalizationInclusion.app Z) := by
    change Mono (inclusionOfMooreComplexMap (freeAbelianSimplicialFunctor.obj Z))
    infer_instance
  exact mono_of_mono_fac (normalizationInclusion.naturality f)

/--
概要：正規化整数鎖写像の余核としての相対鎖複体。
方針：複体のアーベル圏で余核を取る。
規約：部分複体の包含に対して通常の商複体を与える。
使われ方：相対整数ホモロジーの定義。
-/
def relativeIntegralChains {X Y : SSet.{u}} (i : X ⟶ Y) :
    ChainComplex AddCommGrpCat.{u} ℕ := cokernel (normalizedIntegralChains.map i)

/--
概要：可換正方形が誘導する相対鎖写像。
方針：正規化関手で移した正方形に余核の普遍性を適用する。
規約：左右の単体写像と正方形の可換性を明示する。
使われ方：対の写像による相対ホモロジーの関手性。
-/
def relativeIntegralChainsMap {X Y X' Y' : SSet.{u}} (i : X ⟶ Y) (i' : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (w : i ≫ b = a ≫ i') :
    relativeIntegralChains i ⟶ relativeIntegralChains i' :=
  cokernel.map _ _ (normalizedIntegralChains.map a) (normalizedIntegralChains.map b)
    (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, w])

/--
概要：単体写像の圏から相対整数鎖複体への関手。
方針：対象を余核、可換正方形を誘導余核写像へ送る。
規約：一般の写像に対する余核の関手である。
使われ方：相対ホモロジーの恒等・合成との整合。
-/
def relativeIntegralChainsFunctor : Arrow SSet.{u} ⥤ ChainComplex AddCommGrpCat.{u} ℕ where
  obj i := relativeIntegralChains i.hom
  map f := relativeIntegralChainsMap _ _ f.left f.right f.w.symm
  map_id i := by
    apply (cancel_epi (cokernel.π (normalizedIntegralChains.map i.hom))).mp
    simp [relativeIntegralChainsMap, relativeIntegralChains]
  map_comp {i j k} f g := by
    apply (cancel_epi (cokernel.π (normalizedIntegralChains.map i.hom))).mp
    simp [relativeIntegralChainsMap, relativeIntegralChains,
      Category.assoc, CategoryTheory.Functor.map_comp]

/--
概要：相対整数ホモロジーの関手。
方針：余核複体の関手に実際のホモロジーを合成する。
規約：自然数次数。
使われ方：セル添付での相対ホモロジー。
-/
def relativeIntegralHomologyFunctor (n : ℕ) : Arrow SSet.{u} ⥤ AddCommGrpCat.{u} :=
  relativeIntegralChainsFunctor ⋙ HomologicalComplex.homologyFunctor _ _ n

/--
概要：単体写像に対する余核模型の相対整数ホモロジー群。
方針：構成した相対ホモロジー関手の対象を取る。
規約：包含の商複体での計算に用いる。
使われ方：相対群の値。
-/
abbrev relativeIntegralHomology {X Y : SSet.{u}} (i : X ⟶ Y) (n : ℕ) : AddCommGrpCat.{u} :=
  (relativeIntegralHomologyFunctor n).obj (Arrow.mk i)

/--
概要：正規化鎖写像とその余核による完全な三項複体。
方針：アーベル圏の余核列を使う。
規約：左端の単射性は別に要求する。
使われ方：相対ホモロジーの長完全列。
-/
def relativeIntegralChainsSequence {X Y : SSet.{u}} (i : X ⟶ Y) :
    ShortComplex (ChainComplex AddCommGrpCat.{u} ℕ) :=
  ShortComplex.cokernelSequence (normalizedIntegralChains.map i)

/--
概要：正規化鎖写像が単射なら相対鎖複体との列は短完全である。
方針：余核列の完全性と与えられた単射性を使う。
規約：元の単体写像が単射である場合に述べる。
使われ方：包含の相対ホモロジー長完全列を構成する。
-/
theorem relativeIntegralChainsSequence_shortExact {X Y : SSet.{u}} (i : X ⟶ Y)
    [Mono i] : (relativeIntegralChainsSequence i).ShortExact := by
  change (ShortComplex.cokernelSequence (normalizedIntegralChains.map i)).ShortExact
  exact {
    exact := ShortComplex.cokernelSequence_exact _
    mono_f := by
      change Mono (normalizedIntegralChains.map i)
      infer_instance }

/--
概要：相対整数ホモロジーの連結準同型。
方針：構成した短完全列に Mathlib の蛇補題による連結射を適用する。
規約：包含に対し H_(n+1)(Y,X) から H_n(X) へ向かう。
使われ方：相対ホモロジー長完全列。
-/
def relativeIntegralHomologyBoundary {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] (n : ℕ) :
    relativeIntegralHomology i (n + 1) ⟶ integralHomology X n :=
  (relativeIntegralChainsSequence_shortExact i).δ (n + 1) n rfl

/--
概要：相対ホモロジーへの射と連結準同型の合成は零である。
方針：短完全列のホモロジー列の連続する射の零合成を使う。
規約：包含と全自然数次数。
使われ方：長完全列の相対群での完全性。
-/
@[reassoc] theorem relativeIntegralHomology_comp_boundary {X Y : SSet.{u}}
    (i : X ⟶ Y) [Mono i] (n : ℕ) :
    HomologicalComplex.homologyMap (cokernel.π (normalizedIntegralChains.map i)) (n + 1) ≫
      relativeIntegralHomologyBoundary i n = 0 :=
  (relativeIntegralChainsSequence_shortExact i).comp_δ (n + 1) n rfl

/--
概要：連結準同型と包含のホモロジー射の合成は零である。
方針：蛇補題で構成された連結射の零合成を使う。
規約：実際の正規化整数ホモロジーに対する式。
使われ方：長完全列の部分単体集合の群での完全性。
-/
@[reassoc] theorem relativeIntegralHomology_boundary_comp {X Y : SSet.{u}}
    (i : X ⟶ Y) [Mono i] (n : ℕ) :
    relativeIntegralHomologyBoundary i n ≫ integralHomologyMap i n = 0 :=
  (relativeIntegralChainsSequence_shortExact i).δ_comp (n + 1) n rfl

/--
概要：相対ホモロジー長完全列は H_n(X) で完全である。
方針：短完全列のホモロジー列の第一の完全性を適用する。
規約：連結射から包含の誘導射へ続く部分。
使われ方：セル添付のホモロジーの計算。
-/
theorem relativeIntegralHomology_exact_at_source {X Y : SSet.{u}}
    (i : X ⟶ Y) [Mono i] (n : ℕ) :
    (ShortComplex.mk (relativeIntegralHomologyBoundary i n) (integralHomologyMap i n)
      (relativeIntegralHomology_boundary_comp i n)).Exact :=
  (relativeIntegralChainsSequence_shortExact i).homology_exact₁ (n + 1) n rfl

/--
概要：相対ホモロジー長完全列は H_n(Y) で完全である。
方針：構成した短完全列をホモロジーへ移し、第二の完全性を使う。
規約：包含の誘導射から相対群への射へ続く部分。
使われ方：相対群の消滅からのホモロジー比較。
-/
theorem relativeIntegralHomology_exact_at_target {X Y : SSet.{u}}
    (i : X ⟶ Y) [Mono i] (n : ℕ) :
    ((relativeIntegralChainsSequence i).map
      (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) n)).Exact :=
  (relativeIntegralChainsSequence_shortExact i).homology_exact₂ n

/--
概要：相対ホモロジー長完全列は H_(n+1)(Y,X) で完全である。
方針：短完全列のホモロジー列の第三の完全性を適用する。
規約：相対群への射から連結射へ続く部分。
使われ方：セル添付の相対群の計算。
-/
theorem relativeIntegralHomology_exact_at_relative {X Y : SSet.{u}}
    (i : X ⟶ Y) [Mono i] (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (cokernel.π (normalizedIntegralChains.map i)) (n + 1))
      (relativeIntegralHomologyBoundary i n) (relativeIntegralHomology_comp_boundary i n)).Exact :=
  (relativeIntegralChainsSequence_shortExact i).homology_exact₃ (n + 1) n rfl

end SerrePositivity.KST.Comparison
