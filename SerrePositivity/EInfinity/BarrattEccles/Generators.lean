module

public import SerrePositivity.EInfinity.BarrattEccles.Basis
public import Mathlib.AlgebraicTopology.DoldKan.Degeneracies

/-!
# Barratt–Eccles 正規化鎖の単体生成元

概要：Berger–Fresse §1.1.2 の置換列の鎖を正規化 Moore 複体の元として定義する。
方針：自由単体加群の標準生成元に Dold–Kan の正規化射影を適用する。
規約：このファイルでは自然数次数の鎖を扱い、退化単体の生成元は零となる。
使われ方：shuffle の合成公式と微分との両立性を生成元で記述する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open CategoryTheory.Idempotents
open scoped Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：EΣₙ の自然数次数の正規化鎖（Berger–Fresse §1.1.2）。
方針：自由単体加群に正規化 Moore 関手を適用する。
規約：整数コチェイン E(n) の次数 −q に対応する鎖次数 q を持つ。
使われ方：shuffle の微分の計算を自然数次数で行う。 -/
abbrev normalizedChains (n : ℕ) : ChainComplex (ModuleCat A) ℕ :=
  (AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).obj
    ((linearization A).obj (simplicial n))

/-- 概要：交代面鎖複体から正規化鎖への射影（Berger–Fresse §1.1.2）。
方針：Dold–Kan の射影 P∞ を正規化 Moore 部分複体へ因子化する。
規約：鎖写像として定義し、微分との可換性を継承する。
使われ方：任意の置換列の正規化鎖を生成する。 -/
def normalizationMap (n : ℕ) :
    (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat A)).obj
      ((linearization A).obj (simplicial n)) ⟶ normalizedChains A n :=
  AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex _

/-- 概要：置換列が表す正規化鎖の生成元（Berger–Fresse §1.1.2）。
方針：自由加群の一つの標準生成元を正規化する。
規約：退化している列も引数として許す。
使われ方：shuffle 和の各項と微分を明示する。 -/
def normalizedGenerator (n q : ℕ) (x : (simplicial n) _⦋q⦌) :
    (normalizedChains A n).X q :=
  (normalizationMap A n).f q (ModuleCat.freeMk (ULift.up x))

/-- 概要：自由加群化した単体構造射は標準生成元を対応する単体に送る（Berger–Fresse §1.1.2）。
方針：自由加群関手の生成元の像を計算する。
規約：任意の単体圏の反対射について成立する。
使われ方：面・退化写像の鎖生成元への作用を計算する。 -/
lemma linearization_map_freeMk (n : ℕ) {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ')
    (x : (simplicial n).obj Δ) :
    ((linearization A).obj (simplicial n)).map f (ModuleCat.freeMk (ULift.up x)) =
      ModuleCat.freeMk (ULift.up ((simplicial n).map f x)) :=
  ModuleCat.free_map_apply _ _

/-- 概要：正規化射影は退化写像を零にする（Berger–Fresse §1.1.2）。
方針：Moore 部分複体への包含で検査し、退化写像と P∞ の合成の消滅を使う。
規約：次数 q から q+1 への退化写像を扱う。
使われ方：退化単体の生成元が零であることを示す。 -/
lemma σ_normalizationMap (n q : ℕ) (i : Fin (q + 1)) :
    ((linearization A).obj (simplicial n)).σ i ≫ (normalizationMap A n).f (q + 1) = 0 := by
  let X := (linearization A).obj (simplicial n)
  apply (cancel_mono (AlgebraicTopology.NormalizedMooreComplex.objX X (q + 1)).arrow).1
  have h := congrArg (fun f => f.f (q + 1))
    (AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap X)
  change (normalizationMap A n).f (q + 1) ≫
    (AlgebraicTopology.NormalizedMooreComplex.objX X (q + 1)).arrow =
      (AlgebraicTopology.DoldKan.PInfty : _ ⟶ _).f (q + 1) at h
  rw [Category.assoc, h, AlgebraicTopology.DoldKan.σ_comp_PInfty, CategoryTheory.Limits.zero_comp]

/-- 概要：退化写像から得た単体の生成元は零である（Berger–Fresse §1.1.2）。
方針：退化写像と正規化射影の消滅を標準生成元で評価する。
規約：任意の退化位置 i を許す。
使われ方：shuffle の退化項を消去する。 -/
lemma normalizedGenerator_σ (n q : ℕ) (i : Fin (q + 1)) (x : (simplicial n) _⦋q⦌) :
    normalizedGenerator A n (q + 1) ((simplicial n).σ i x) = 0 := by
  have h := congrArg (fun f => f (ModuleCat.freeMk (ULift.up x))) (σ_normalizationMap A n q i)
  change (normalizationMap A n).f (q + 1)
    (((linearization A).obj (simplicial n)).σ i (ModuleCat.freeMk (ULift.up x))) = 0 at h
  rw [show ((linearization A).obj (simplicial n)).σ i (ModuleCat.freeMk (ULift.up x)) =
    ModuleCat.freeMk (ULift.up ((simplicial n).σ i x)) from linearization_map_freeMk A n _ x] at h
  exact h

/-- 概要：任意の退化単体が表す正規化鎖は零である（Berger–Fresse §1.1.2）。
方針：退化集合を一つの退化写像の像の和として表す。
規約：0 単体の退化集合は空である。
使われ方：非退化な置換列だけを正規化鎖の基底に残す。 -/
lemma normalizedGenerator_degenerate (n q : ℕ) (x : (simplicial n) _⦋q⦌)
    (hx : x ∈ (simplicial n).degenerate q) : normalizedGenerator A n q x = 0 := by
  cases q with
  | zero => simp at hx
  | succ q =>
    rw [SSet.degenerate_eq_iUnion_range_σ] at hx
    obtain ⟨i, y, rfl⟩ := Set.mem_iUnion.mp hx
    exact normalizedGenerator_σ A n q i y

/-- 概要：生成元の微分は頂点を一つずつ除く交代和である（Berger–Fresse §1.1.2）。
方針：正規化射影の鎖写像の等式を標準生成元で評価する。
規約：鎖次数 q+1 から q への微分で、符号は (−1)^i。
使われ方：shuffle の合成が微分と可換することを生成元で確認する。 -/
lemma normalizedGenerator_d (n q : ℕ) (x : (simplicial n) _⦋q + 1⦌) :
    (normalizedChains A n).d (q + 1) q (normalizedGenerator A n (q + 1) x) =
      ∑ i : Fin (q + 2), (-1 : ℤ) ^ i.val •
        normalizedGenerator A n q ((simplicial n).δ i x) := by
  have h := congrArg (fun f => f (ModuleCat.freeMk (ULift.up x)))
    ((normalizationMap A n).comm (q + 1) q)
  change (normalizedChains A n).d (q + 1) q (normalizedGenerator A n (q + 1) x) =
    (normalizationMap A n).f q
      (((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat A)).obj
        ((linearization A).obj (simplicial n))).d (q + 1) q
          (ModuleCat.freeMk (ULift.up x))) at h
  rw [h]
  erw [AlgebraicTopology.alternatingFaceMapComplex_obj_d]
  simp [normalizedGenerator, SimplicialObject.δ, linearization_map_freeMk]

/-- 概要：非退化部分の包含を正規化すると Moore 比較同型になる（Berger–Fresse §1.1.2）。
方針：Karoubi 包絡の比較射の像を成分で評価し、P∞ の冪等性を使う。
規約：鎖次数 q における加群の射の等式。
使われ方：正規化生成元を既存の非退化基底と同定する。 -/
lemma ι_normalizationMap (n q : ℕ) :
    (linearSplitting A n).ι q ≫ (normalizationMap A n).f q =
      (nondegenerateChainIso A n).hom.f q := by
  let X := (linearization A).obj (simplicial n)
  let e := (linearSplitting A n).toKaroubiNondegComplexIsoN₁ ≪≫
    (AlgebraicTopology.DoldKan.N₁_iso_normalizedMooreComplex_comp_toKaroubi (ModuleCat A)).app X
  have hm : (toKaroubi _).map (nondegenerateChainIso A n).hom = e.hom :=
    CategoryTheory.Functor.map_preimage _ _
  have h := congrArg (fun f => f.f.f q) hm
  change (nondegenerateChainIso A n).hom.f q =
    (((linearSplitting A n).cofan _).inj
      (SimplicialObject.Splitting.IndexSet.id _ ) ≫
        (AlgebraicTopology.DoldKan.PInfty (X := X)).f q) ≫
      (normalizationMap A n).f q at h
  have hp := congrArg (fun f => f.f q)
    (AlgebraicTopology.DoldKan.PInfty_comp_PInftyToNormalizedMooreComplex X)
  change (AlgebraicTopology.DoldKan.PInfty (X := X)).f q ≫
    (normalizationMap A n).f q = (normalizationMap A n).f q at hp
  rw [Category.assoc, hp] at h
  simpa [SimplicialObject.Splitting.cofan, SimplicialObject.Splitting.IndexSet.id,
    SimplicialObject.Splitting.IndexSet.e] using h.symm

/-- 概要：非退化単体の正規化生成元は比較同型による基底ベクトルである（Berger–Fresse §1.1.2）。
方針：非退化部分の包含と正規化の等式を標準生成元で評価する。
規約：単体の非退化性を部分型で指定する。
使われ方：非退化生成元による線形写像の構成と一意性に用いる。 -/
lemma normalizedGenerator_nondegenerate (n q : ℕ) (x : (simplicial n).nonDegenerate q) :
    normalizedGenerator A n q x.val =
      (nondegenerateChainIso A n).hom.f q (ModuleCat.freeMk (ULift.up x)) := by
  have h := congrArg (fun f => f (ModuleCat.freeMk (ULift.up x))) (ι_normalizationMap A n q)
  change (normalizationMap A n).f q
    ((linearSplitting A n).ι q (ModuleCat.freeMk (ULift.up x))) = _ at h
  have hι : (linearSplitting A n).ι q (ModuleCat.freeMk (ULift.up x)) =
      ModuleCat.freeMk (ULift.up x.val) := ModuleCat.free_map_apply _ _
  rw [hι] at h
  exact h

/-- 概要：非退化生成元はコチェインの基底と次数移送で一致する（Berger–Fresse §1.1.2）。
方針：自由加群表示の逆同型と次数移送の同型を消去する。
規約：コチェイン次数 −q を鎖次数 q と比較する。
使われ方：自然数次数で構成した shuffle を E(n) に移す。 -/
lemma complexXIso_basis (n q : ℕ) (x : (simplicial n).nonDegenerate q) :
    (complexXIso A n q).hom (complexBasis A n q (ULift.up x)) =
      normalizedGenerator A n q x.val := by
  change (complexXIso A n q).toLinearEquiv
      ((complexXIso A n q).toLinearEquiv.symm
        ((nondegenerateChainIso A n).hom.f q (ModuleCat.freeMk (ULift.up x)))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact (normalizedGenerator_nondegenerate A n q x).symm

/-- 概要：正規化鎖からの線形射は単体生成元上で決まる（Berger–Fresse §1.1.2）。
方針：非退化鎖の自由加群からの同型を前合成し、標準生成元で検査する。
規約：退化単体の像に別の条件を課さず、生成元上の一致のみ要求する。
使われ方：shuffle の鎖写像や代数的恒等式を生成元上の計算へ帰着する。 -/
lemma normalizedGenerator_hom_ext (n q : ℕ) {M : ModuleCat A}
    (f g : (normalizedChains A n).X q ⟶ M)
    (h : ∀ x : (simplicial n) _⦋q⦌, f (normalizedGenerator A n q x) =
      g (normalizedGenerator A n q x)) : f = g := by
  apply (cancel_epi ((HomologicalComplex.eval _ _ q).mapIso (nondegenerateChainIso A n)).hom).1
  apply ModuleCat.free_hom_ext
  intro x
  have hx := h x.down.val
  rw [normalizedGenerator_nondegenerate] at hx
  exact hx

end SerrePositivity.EInfinity.BarrattEccles
