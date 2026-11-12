-- 将来の置き場所：SerrePositivity.EInfinity.Descendable.*（新設。調整役の決定、main 86acd98db、M15。E∞ を使わない thick ⊗-ideal・index・安定性は Derived/ へ下ろしてよい。時期・担当は段 G、A5 の中身の段階で）
-- 設計書：formalization-plans/bhatt-scholze/a5-design.md §2.4、G-A5-1。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.EInfinity.Perfectoidization.TheoryInterface
public import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.FinitePresentation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianPathSpace
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseLimits
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeEquiv
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.NativeConeLeg
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SquareDiagonal
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Stability
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Suspension
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Loop
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.Fixed
-- 取り込み時の依存先：drafts/DerivedGeneral/{ScalarRestriction,CompletionFunctor}.lean。

/-!
# descendability（[Mat16, Def 3.18]、[BS17, §11.2]）

## 概要
可換環 A 上の E∞ 代数 B（CAlg_A の対象、射 A → B）が descendable とは、D(A) の中で B の生成する thick ⊗-ideal（有限余極限・retract・shift・
任意の対象とのテンソルで閉じた最小の充満部分圏）が単位 A を含むこと。index は fib(A → B)^{⊗n} → A が零になる最小の n。
性質：(a) 底変換、(b) 合成、(c) テンソル、(d) index による判定、(e) 降下 M ≃ Tot(M ⊗_A B^{⊗•+1})（[Mat16, Prop 3.22]）、
(f) RHom_A(F^{⊗2}, A) ∈ D^{<0} ⇒ index ≤ 2、(g) [BS17, Lemma 11.22]（φ と両立する index ≤ n の colim_φ は index ≤ 2n）、(h) 完備版。

## 方針
定義は原典の引用どおり [Mat16] の thick ⊗-ideal（決定 2、D49）。index の判定 (d) は定理。(e) は Tot の塔の分裂（fib^{⊗n} → A 零 ⇒
Amitsur 複体の部分 Tot が retract）。

## 規約
D(A) は `derivedInfinityCategory A`、テンソルは導来テンソル。完備版 (h) は D_comp(A) の完備テンソルで同じ定義。

## 使われ方
Lemma 8.6（A5-3）、Prop 8.5 の降下（A5-4）。
-/

@[expose] public section
noncomputable section
universe u

variable (E : SerrePositivity.EInfinity.EInfinityTheory.{u})

namespace SerrePositivity.EInfinity

open CategoryTheory Limits SSet MonoidalCategory MonoidalClosed
open SerrePositivity.InfinityCategories Perfectoidization
open SerrePositivity.BhattScholze.PerfectoidizationInterface (ofAlgebra)
open scoped Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：D(A) の充満部分圏（頂点の述語）が thick ⊗-ideal：有限余極限・retract・shift・任意の対象とのテンソルで閉じる。
方針：述語の閉性の構造。
規約：`(derivedInfinityCategory A) _⦋0⦌ → Prop`。
使われ方：`thickTensorIdealGenerated`。 -/
structure IsThickTensorIdeal (P : (derivedInfinityCategory A) _⦋0⦌ → Prop) : Prop where
  finiteColimits : ∀ {K : SSet.{u+1}} [K.Finite] (F : K ⟶ derivedInfinityCategory A)
    (c : JoinCocone F), (∀ i, P (F.app _ i)) → IsColimitCone c → P c.vertex
  retracts : ∀ {x y} (i : SSet.Edge x y) (r : SSet.Edge y x),
    Truncated.HomotopyCategory.homMk i.toTruncated ≫ Truncated.HomotopyCategory.homMk r.toTruncated =
      𝟙 (HomotopyCategory.mk x) → P y → P x
  shifts : ∀ x, P x →
    P (((suspensionFunctor (derivedInfinityCategory A)).obj (HomotopyCategory.mk x)).pt) ∧
    P (((loopFunctor (derivedInfinityCategory A)).obj (HomotopyCategory.mk x)).pt)
  -- tensorWith は Derived/Tensor/Fixed（IF-G1 ⊗ᴸ、main 7bda72c3c）。N ↦ N ⊗ᴸ M
  tensor : ∀ (x M : (derivedInfinityCategory A) _⦋0⦌), P x → P ((tensorWith M).app _ x)

/-- 概要：対象 M の生成する thick ⊗-ideal（M を含む thick ⊗-ideal の sInf）。
方針：述語の ∀ による交わり。
規約：—
使われ方：`IsDescendable`。 -/
def thickTensorIdealGenerated (M : (derivedInfinityCategory A) _⦋0⦌) : (derivedInfinityCategory A) _⦋0⦌ → Prop :=
  fun N => ∀ P, IsThickTensorIdeal A P → P M → P N

/-- CAlg_A の始対象 A。ここからの辺は各代数の構造射を表す。 -/
abbrev unitAlgebra := (E.discrete A).app _ (nerveVertex (Under.mk (𝟙 (CommRingCat.of A))))

/-- 概要：[Mat16, Def 3.18]：A → B（CAlg_A の対象 B）が descendable ⇔ B の生成する thick ⊗-ideal が単位 A を含む。
方針：定義どおり。
規約：B は `(CAlg_R A) _⦋0⦌`、底の D(A) 対象は忘却。**W9-II-13**：これは離散環 A を底とする特殊化。Lemma 8.6 の Δ_T → Δ_{T_∞} は E∞ 代数 Δ_T を底とする
射なので、一般形は「対称モノイダルな安定 ∞ 圏 𝒞 の可換代数対象 B と Mod_B(𝒞) の thick ⊗-ideal」で定義する（`IsDescendableOver`、下）。
使われ方：以下すべて。 -/
def IsDescendable (B : (E.CAlg A) _⦋0⦌) : Prop :=
  thickTensorIdealGenerated A ((E.forget A).app _ B)
    ((E.forget A).app _ (unitAlgebra (E := E) A))

/-- 概要：一般形（W9-II-13、**入口を確定：11-03、BS-D3 の D3-04**）：CAlg_A の射 f : R → B（R は一般に離散でない E∞-A 代数、例 Δ_T）が descendable ⇔
Mod_R(D(A)) の中で B の生成する thick ⊗-ideal が R を含む（[Mat16, Def 3.18] を 𝒞 = Mod_R に適用）。離散環版 `IsDescendable` は R = 単位対象の特殊化。
方針：Mod_R(D(A))（E∞ 代数 R 上の加群の安定 ∞ 圏）とその thick ⊗-ideal は基盤側（M15。EInfinity に加群の ∞ 圏がなければ Derived/ に下ろして作る）。
A5 はこの Prop と下の API だけを使い、Mod_R の構成には触れない。
規約：R・B は `(CAlg_R A) _⦋0⦌`、f は `SSet.Edge R B`。完備版（Lemma 8.6 の D_comp(A)）は R・B が完備な対象のときの同じ定義（(h)）。
使われ方：Lemma 8.6（A5-3：R = Δ_T、B = Δ_{T_∞}）、A5-4 の降下。 -/
def IsDescendableOver (R B : (E.CAlg A) _⦋0⦌) (f : SSet.Edge R B) : Prop := sorry -- 基盤待ち（M15）：Mod_R(D(A)) の thick ⊗-ideal

/-- 概要：一般形の index ≤ n：F := fib(R → B)（Mod_R の対象）について F^{⊗_R n} → R が Mod_R で零（[BS17, §11.2]）。
方針：Mod_R の相対テンソルと fiber。
規約：基盤待ち。
使われ方：(d)(f)(g) の一般形。 -/
def HasDescentIndexLEOver (R B : (E.CAlg A) _⦋0⦌) (f : SSet.Edge R B) (n : ℕ) : Prop := sorry -- 基盤待ち（M15）

/-- 概要：(d) の一般形：descendable ⇔ ∃ n, index ≤ n。 -/
theorem isDescendableOver_iff_exists_index (R B : (E.CAlg A) _⦋0⦌) (f : SSet.Edge R B) :
    IsDescendableOver (E := E) A R B f ↔ ∃ n, HasDescentIndexLEOver (E := E) A R B f n := by sorry -- 基盤待ち

/-- 概要：離散環版との一致：R が CAlg_A の単位対象（A の埋め込み）で f が B の構造射なら `IsDescendableOver A R B f ↔ IsDescendable A B`。
方針：Mod_{1} = D(A)。単位は離散 A の像で、そこから B への辺は構造射。
規約：基盤待ち。 -/
theorem isDescendableOver_unit_iff (B : (E.CAlg A) _⦋0⦌) (f : SSet.Edge (unitAlgebra (E := E) A) B) :
    IsDescendableOver (E := E) A _ B f ↔ IsDescendable (E := E) A B := by
  sorry -- Mod_A(D(A)) は D(A)

/-- 概要：(a) の一般形：f : R → B descendable、g : R → R′ なら R′ → B ⊔_R R′（CAlg_A の押し出し＝相対テンソル B ⊗_R R′）も descendable（index も保つ）。
方針：Mod_R → Mod_{R′} の底変換は thick ⊗-ideal を保つ。押し出しの名前は A7 `relativeTensor` の E∞ 版（基盤待ち）。
規約：基盤待ち。A5-4 の降下（Δ_T → Δ_S に沿う底変換）で使う。 -/
theorem isDescendableOver_pushout (Q : (Δ[1] ⊗ Δ[1] : SSet.{u+1}) ⟶ E.CAlg A)
    (hQ : IsColimitCone (pushoutCocone Q)) (h : IsDescendableOver (E := E) A _ _ (.ofTruncated (squareBottomArrow Q))) :
    IsDescendableOver (E := E) A _ _ (.ofTruncated (squareTopArrow Q)) := by
  sorry -- Mod_R の底変換は thick ⊗-ideal を保つ

theorem hasDescentIndexLEOver_pushout (Q : (Δ[1] ⊗ Δ[1] : SSet.{u+1}) ⟶ E.CAlg A)
    (hQ : IsColimitCone (pushoutCocone Q)) (n : ℕ)
    (h : HasDescentIndexLEOver (E := E) A _ _ (.ofTruncated (squareBottomArrow Q)) n) :
    HasDescentIndexLEOver (E := E) A _ _ (.ofTruncated (squareTopArrow Q)) n := by
  sorry -- fiber の n 重テンソルの零写像を底変換する

/-- 概要：(b)(c) の一般形：合成と相対テンソル。合成の辺の指定（quasicategory の合成の証人）は基盤の名前が決まってから。 -/
theorem isDescendableOver_comp {R B C : (E.CAlg A) _⦋0⦌} (f : SSet.Edge R B)
    (g : SSet.Edge B C) (h : SSet.Edge R C) (σ : SSet.Edge.CompStruct f g h)
    (hf : IsDescendableOver (E := E) A R B f) (hg : IsDescendableOver (E := E) A B C g) :
    IsDescendableOver (E := E) A R C h := by
  sorry -- R 加群への制限と thick ⊗-ideal の生成の推移性

theorem isDescendableOver_tensor (Q : (Δ[1] ⊗ Δ[1] : SSet.{u+1}) ⟶ E.CAlg A)
    (hQ : IsColimitCone (pushoutCocone Q))
    (hf : IsDescendableOver (E := E) A _ _ (.ofTruncated (squareBottomArrow Q)))
    (hg : IsDescendableOver (E := E) A _ _ (.ofTruncated (squareLeftArrow Q))) :
    IsDescendableOver (E := E) A _ _ (.ofTruncated (squareDiagonalArrow Q)) := by
  sorry -- 押し出しの上辺への底変換と左辺の合成

/-- 射の ∞ 圏の頂点 v を、実際の一単体に戻す。 -/
abbrev algebraArrow := (ihom (Δ[1] : SSet.{u+1})).obj (E.CAlg A)
def algebraArrowEdge (v : (algebraArrow (E := E) A) _⦋0⦌) :=
  SSet.Edge.ofTruncated (intervalFunctorVertexTypedEdge v)

/-- A5 の別々の始域をもつ二本の射のテンソル。射の圏の余積は両端での A 上のテンソル。 -/
theorem isDescendableOver_tensorMaps (D : (SSet.uliftFunctor.{u+1,0}).obj (nerve (Discrete (Fin 2))) ⟶ algebraArrow (E := E) A)
    (c : JoinCocone D) (hc : IsColimitCone c)
    (h : ∀ j : Fin 2, IsDescendableOver (E := E) A _ _ (algebraArrowEdge (E := E) A (D.app _ (ULift.up (nerveVertex (Discrete.mk j)))))) :
    IsDescendableOver (E := E) A _ _ (algebraArrowEdge (E := E) A c.vertex) := by
  sorry -- 各辺を他の始域・終域に沿って底変換し、二辺を合成

/-- 増大添字の [−1] → [n] の錐。 -/
def augmentationIndexCone : Cone AugmentedSimplexCategory.inclusion where
  pt := .star
  π := { app := WithInitial.homTo, naturality := by intros; rfl }

/-- [−1] を中心、n+1 個の [0] を枝とする図式。その余錐の脚は全ての頂点 [0] → [n]。 -/
abbrev amitsurStar (n : ℕ) : WithInitial (Discrete (Fin (n+1))) ⥤ AugmentedSimplexCategory :=
  WithInitial.map ((Functor.const _).obj ⦋0⦌)

def amitsurTermCone (n : ℕ) : Cocone (amitsurStar n) where
  pt := .of ⦋n⦌
  ι := {
    app := fun j => match j with
      | .star => WithInitial.homTo ⦋n⦌
      | .of i => AugmentedSimplexCategory.inclusion.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i.as)
    naturality := by sorry } -- 中心からの射は一意、枝の間には恒等射しかない

abbrev augmentedShape := (SSet.uliftFunctor.{u+1,0}).obj (nerve AugmentedSimplexCategory)

def amitsurAug (D : augmentedShape.{u} ⟶ E.CAlg A) :=
  mapJoinCone D (JoinCone.ulift.{0,u+1} (F1B.nerveCone augmentationIndexCone))

/-- D の増大と各段の脚・高次の整合性を同じ増大図式から制限する。
各段の余極限条件が R を底とする B の (n+1) 重押し出しを指定する。 -/
structure AmitsurData {R B : (E.CAlg A) _⦋0⦌} (f : SSet.Edge R B) where
  diagram : augmentedShape.{u} ⟶ E.CAlg A
  base : VertexIso R (amitsurAug (E := E) A diagram).vertex
  zero : VertexIso (diagram.app _ (ULift.up (nerveVertex (WithInitial.of ⦋0⦌)))) B
  leg : base.hom ≫ Truncated.HomotopyCategory.homMk
      (F2.nativeConeLeg (amitsurAug (E := E) A diagram) (ULift.up (nerveVertex ⦋0⦌))) ≫ zero.hom =
    Truncated.HomotopyCategory.homMk f.toTruncated
  term (n : ℕ) : IsColimitCone (mapJoinCocone diagram
    (JoinCocone.ulift.{0,u+1} (F1B.nerveCoconeEquiv (amitsurTermCone n))))

abbrev AmitsurData.aug {A : Type u} [CommRing A] {R B : (E.CAlg A) _⦋0⦌} {f : SSet.Edge R B} (d : AmitsurData (E := E) A f) :=
  amitsurAug (E := E) A d.diagram

/-- 概要：(e) の一般形 [Mat16, Prop 3.22]：f : R → B descendable なら任意の R 加群 M について M ≃ Tot(M ⊗_R B^{⊗_R (•+1)})。A5-4 では M = R = Δ_T。
方針：index n で Tot_{≤n} の塔が分裂。Tot は HomotopyLimits（S3 と同じ）。
規約：基盤待ち。 -/
theorem isDescendableOver_tot_equiv {R B : (E.CAlg A) _⦋0⦌} (f : SSet.Edge R B)
    (hf : IsDescendableOver (E := E) A R B f) (d : AmitsurData (E := E) A f) : IsLimitCone d.aug := by
  sorry -- M = R。index による Amitsur 塔の分裂と忘却の極限反映

/-- 概要：(f) の一般形：F := fib(R → B)、RHom_R(F^{⊗_R 2}, R) ∈ D^{≤−1}（Mod_R の内部 Hom。A5 StrongDescent の RHom_{Δ_T}）なら F^{⊗_R 2} → R は零で index ≤ 2。
方針：π_0 RHom = 0。
規約：×。Mod_R の内部 Hom の ∞ 関手が未実装。Lemma 8.6 の n = 1 で使う。 -/
theorem hasDescentIndexLEOver_two_of_rhom : True := by trivial -- 基盤待ち

/-- 概要：(g)(h) の一般形：Frobenius 余極限（[BS17, Lemma 11.22]、index ≤ n ⇒ colim_φ で ≤ 2n）と完備版（完備な R・B で同じ定義）。 -/
theorem hasDescentIndexLEOver_frobeniusColimit
    (D : (SSet.uliftFunctor.{u+1,0}).obj (nerve ℕ) ⟶ algebraArrow (E := E) A)
    (c : JoinCocone D) (hc : IsColimitCone c) (n : ℕ)
    (h : ∀ j : ℕ, HasDescentIndexLEOver (E := E) A _ _ (algebraArrowEdge (E := E) A (D.app _ (ULift.up (nerveVertex j)))) n) :
    HasDescentIndexLEOver (E := E) A _ _ (algebraArrowEdge (E := E) A c.vertex) (2*n) := by
  sorry -- BS17 Lemma 11.22。射の圏の余極限は両端の余極限と誘導射を同時に指定する

/-- ×：D(A) の導来テンソルは `tensorWith`（IF-G1）で入ったが、一般底 Mod_R の相対完備テンソルは M15 待ち。 -/
theorem isDescendableOver_complete : True := by trivial -- 基盤待ち

/-- 概要：index ≤ n：fib(A → B)^{⊗n} → A が零（[BS17, §11.2]）。
方針：fib と導来テンソル冪。
規約：—
使われ方：(d)(f)(g)。 -/
def HasDescentIndexLE (B : (E.CAlg A) _⦋0⦌) (n : ℕ) : Prop := sorry

/-- 概要：(d) descendable ⇔ ∃ n, index ≤ n（[Mat16, Prop 3.? / BS17 Lemma 11.?]）。
方針：⇐：fib^{⊗n} → A 零なら A は B ⊗ (−) の有限個の拡大の retract。⇒：thick ⊗-ideal の生成の帰納。
規約：—
使われ方：(f)(g) から descendable へ。 -/
theorem isDescendable_iff_exists_index (B : (E.CAlg A) _⦋0⦌) : IsDescendable (E := E) A B ↔ ∃ n, HasDescentIndexLE (E := E) A B n := by sorry

/-- 概要：(a) 底変換：A → B descendable、A → A′ なら A′ → B ⊗_A A′ descendable（index も保つ）。 -/
theorem isDescendable_baseChange {A' : Type u} [CommRing A'] (g : A →+* A') (B : (E.CAlg A) _⦋0⦌)
    (hB : IsDescendable (E := E) A B) : IsDescendable (E := E) A' ((cAlgBaseChange (E := E) g).app _ B) := by
  sorry -- unit_iff と (a)。g に沿う cAlgBaseChange の値は A′ ⊔_A B

/-- 概要：(b) 合成：A → B、B → C descendable なら A → C。 -/
theorem isDescendable_comp {B : Type u} [CommRing B] (g : A →+* B)
    (hB : IsDescendable (E := E) A ((E.discrete A).app _ (nerveVertex (Under.mk (CommRingCat.ofHom g)))))
    (C : (E.CAlg B) _⦋0⦌) (hC : IsDescendable (E := E) B C) :
    IsDescendable (E := E) A ((cAlgRestrictScalars (E := E) g).app _ C) := by
  sorry -- 離散 B に沿う構造射の合成に (b) を適用

/-- 概要：(c) テンソル：A → B、A → C descendable なら A → B ⊗_A C（(a) と (b)）。 -/
theorem isDescendable_tensor (Q : (Δ[1] ⊗ Δ[1] : SSet.{u+1}) ⟶ E.CAlg A)
    (hQ : IsColimitCone (pushoutCocone Q)) (hA : VertexIso (squareVertex Q 0 0) (unitAlgebra (E := E) A))
    (hB : IsDescendable (E := E) A (squareVertex Q 1 0)) (hC : IsDescendable (E := E) A (squareVertex Q 0 1)) :
    IsDescendable (E := E) A (squareVertex Q 1 1) := by
  sorry -- 始対象 A 上の押し出しに (c) を適用

/-- 概要：(e) 降下 [Mat16, Prop 3.22]：A → B descendable なら ∀ M ∈ D(A)、M ≃ Tot(M ⊗_A B^{⊗•+1})（Amitsur 複体の全化）。
方針：index n で Tot_{≤n} の塔が分裂。
規約：Tot は HomotopyLimits の全化（S3 の Tot と同じ）。
使われ方：A5-4 の降下。 -/
theorem isDescendable_tot_equiv (B : (E.CAlg A) _⦋0⦌) (hB : IsDescendable (E := E) A B)
    (f : SSet.Edge (unitAlgebra (E := E) A) B) (d : AmitsurData (E := E) A f) : IsLimitCone d.aug := by
  sorry -- isDescendableOver_unit_iff と isDescendableOver_tot_equiv、M = A

/-- 概要：(f) F := fib(A → B)。RHom_A(F^{⊗2}, A) ∈ D^{<0} なら F^{⊗2} → A は零、よって index ≤ 2。
方針：π_0 RHom = 0。
規約：×。D(A) の内部 Hom の ∞ 関手が未実装。
使われ方：Lemma 8.6 の n = 1。 -/
theorem hasDescentIndexLE_two_of_rhom : True := by trivial

/-- 離散環 base からの構造射を共通係数 A 上で読む表示。底が塔とともに動いてよい。
射の圏で比較するため、単に両端を同一視するより強く、構造射自体が対応する。 -/
structure DiscreteSource (v : (algebraArrow (E := E) A) _⦋0⦌) where
  base : Type u
  [ring : CommRing base]
  scalars : A →+* base
  target : (E.CAlg base) _⦋0⦌
  unit : SSet.Edge (unitAlgebra (E := E) base) target
  presentation : VertexIso v (functorVertex (SSet.yonedaEquiv.symm ((unit.map (cAlgRestrictScalars (E := E) scalars)).edge)))

/-- 概要：(g) [BS17, Lemma 11.22]：A → B が index ≤ n で両者に両立する自己準同型 φ があれば、colim_φ A → colim_φ B は index ≤ 2n。
方針：BS17 の議論（余極限の fib のテンソル冪の零性）。
規約：sequential 余極限。
使われ方：Lemma 8.6 の perf 版。 -/
theorem hasDescentIndexLE_frobeniusColimit (D : (SSet.uliftFunctor.{u+1,0}).obj (nerve ℕ) ⟶ algebraArrow (E := E) A)
    (c : JoinCocone D) (hc : IsColimitCone c)
    (s : ∀ j : ℕ, DiscreteSource (E := E) A (D.app _ (ULift.up (nerveVertex j)))) (t : DiscreteSource (E := E) A c.vertex)
    (n : ℕ) (h : ∀ j, @HasDescentIndexLE (E := E) (s j).base (s j).ring (s j).target n) :
    @HasDescentIndexLE (E := E) t.base t.ring t.target (2*n) := by
  sorry -- 各離散底の Mod_base での index を一般形に移し、余極限の離散底で読み戻す

/-- 離散底の完備 thick ⊗-ideal。テンソル積を s で導来完備化する。 -/
structure IsThickCompleteTensorIdeal (s : Finset A)
    (P : (derivedInfinityCategory A) _⦋0⦌ → Prop) : Prop where
  finiteColimits : ∀ {K : SSet.{u+1}} [K.Finite] (F : K ⟶ derivedInfinityCategory A)
    (c : JoinCocone F), (∀ i, P (F.app _ i)) → IsColimitCone c → P c.vertex
  retracts : ∀ {x y} (i : SSet.Edge x y) (r : SSet.Edge y x),
    Truncated.HomotopyCategory.homMk i.toTruncated ≫ Truncated.HomotopyCategory.homMk r.toTruncated =
      𝟙 (HomotopyCategory.mk x) → P y → P x
  shifts : ∀ x, P x →
    P (((suspensionFunctor (derivedInfinityCategory A)).obj (HomotopyCategory.mk x)).pt) ∧
    P (((loopFunctor (derivedInfinityCategory A)).obj (HomotopyCategory.mk x)).pt)
  -- tensorWith は Derived/Tensor/Fixed（IF-G1 ⊗ᴸ、main 7bda72c3c）。N ↦ N ⊗ᴸ M
  tensor : ∀ (x M : (derivedInfinityCategory A) _⦋0⦌), P x →
    P ((tensorWith M ≫ Derived.completion A s).app _ x)

/-- B の生成する完備 thick ⊗-ideal が完備化した単位を含む。 -/
def IsDescendableComplete (s : Finset A) (B : (E.CAlg A) _⦋0⦌) : Prop :=
  ∀ P, IsThickCompleteTensorIdeal A s P → P ((E.forget A).app _ B) →
    P ((E.forget A ≫ Derived.completion A s).app _ (unitAlgebra (E := E) A))

/-- (h) 台が s 完備な B の descendability は、対称モノイダルな局所化である完備化に沿って移る。 -/
theorem isDescendable_complete (s : Finset A) (B : (E.CAlg A) _⦋0⦌)
    (hB : Derived.IsDerivedComplete A s ((E.forget A).app _ B)) :
    IsDescendable (E := E) A B → IsDescendableComplete (E := E) A s B := by
  sorry -- 完備化は有限余極限・retract・shift を保ち、B の完備化は hB により B と同値

/-- 概要：[Mat16, Prop 3.31]、有限表示かつ忠実平坦な離散 A 代数は descendable。忠実平坦だけでは偽（Aoki, arXiv:2411.05995）。A5 では直接使わない記録（D5-04）。 -/
theorem isDescendable_of_faithfullyFlat (B : Type u) [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] [Algebra.FinitePresentation A B] :
    IsDescendable (E := E) A ((E.discrete A).app _ (nerveVertex (ofAlgebra A B))) := by
  sorry -- 有限表示の忠実平坦射への Mathew Prop 3.31 の適用

end SerrePositivity.EInfinity
