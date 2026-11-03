module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Basic

/-!
# Complexes.HomComplex

## 概要
4 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## HomComplex（旧 SerrePositivity/DifferentialGraded/Complexes/HomComplex.lean） -/

/-! # 非有界 A 複体と A 線形 Hom 複体

微分は +1、ホモトピーは −1。環・加群は同じ宇宙 u に置く。
対象の有界性・有限性・環の標数には仮定を置かない。
-/

@[expose] public section HomComplex
universe u

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- 任意の可換環上の整数コチェイン複体。非有界対象を含む。 -/
abbrev Complex := CochainComplex (ModuleCat.{u} A) ℤ

/-- Mathlib の A 線形 Hom 複体を主データとして再利用する。 -/
abbrev homComplex (X Y : Complex A) : Complex A := CochainComplex.linearHomComplex A X Y

variable {A} {X Y Z : Complex A}

/-- 次数 n の線形射の族。Mathlib の Triplet により次数の等式を保持する。 -/
abbrev Homogeneous (X Y : Complex A) (n : ℤ) := Cochain X Y n

/-- Hom 微分の二乗は零。非隣接次数でも成立する。 -/
lemma differential_squared (p q r : ℤ) (f : Homogeneous X Y p) :
    δ q r (δ p q f) = 0 := δ_δ p q r f

/-- 通常順 μ(g,f)=g∘f の Leibniz 則。符号は後に作用する g の次数 q。 -/
lemma differential_comp {p q n : ℤ} (f : Homogeneous X Y p) (g : Homogeneous Y Z q)
    (h : p + q = n) :
    δ n (n + 1) (f.comp g h) =
      f.comp (δ q (q + 1) g) (by omega) +
      q.negOnePow • (δ p (p + 1) f).comp g (by omega) :=
  δ_comp f g h (p + 1) (q + 1) (n + 1) rfl rfl rfl

/-- 閉次数零の射と chain map の A 線形同値。 -/
def closedZeroEquiv (X Y : Complex A) : (X ⟶ Y) ≃ₗ[A] Cocycle X Y 0 :=
  { Cocycle.equivHom X Y with map_smul' := Cocycle.ofHom_smul }

/-- contracting homotopy は次数 −1、その境界が恒等射なら対象を収縮する。 -/
def contractingHomotopy (X : Complex A)
    (h : Homogeneous X X (-1)) (dh : δ (-1) 0 h = Cochain.ofHom (𝟙 X)) :
    Homotopy (𝟙 X) 0 :=
  (Cochain.equivHomotopy (𝟙 X) 0).symm ⟨h, by simp [dh]⟩
end SerrePositivity.DifferentialGraded
end

end HomComplex

/-! ## HomFunctor（旧 SerrePositivity/DifferentialGraded/Complexes/HomFunctor.lean） -/

/-! # linearHomComplex の両変数関手性 -/

@[expose] public section HomFunctor
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- Hom 複体の値域での後合成。次数を変えず微分と可換。 -/
def homPostcompose (P : Complex A) {Q T : Complex A} (f : Q ⟶ T) :
    homComplex A P Q ⟶ homComplex A P T where
  f n := ModuleCat.ofHom
    { toFun z := z.comp (Cochain.ofHom f) (add_zero n)
      map_add' z z' := Cochain.add_comp z z' _ _
      map_smul' a z := Cochain.smul_comp a z _ _ }
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact δ_comp_ofHom z f m

/-- Hom 複体の原変数での前合成。 -/
def homPrecompose {P Q : Complex A} (f : P ⟶ Q) (T : Complex A) :
    homComplex A Q T ⟶ homComplex A P T where
  f n := ModuleCat.ofHom
    { toFun z := (Cochain.ofHom f).comp z (zero_add n)
      map_add' z z' := Cochain.comp_add _ z z' _
      map_smul' a z := Cochain.comp_smul _ a z _ }
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact δ_ofHom_comp f z m

/-- 後合成の成分公式。 -/
@[simp]
lemma homPostcompose_apply (P : Complex A) {Q T : Complex A} (f : Q ⟶ T)
    (n : ℤ) (z : Homogeneous P Q n) :
    (homPostcompose P f).f n z = z.comp (Cochain.ofHom f) (add_zero n) := rfl

/-- 前合成の成分公式。 -/
@[simp]
lemma homPrecompose_apply {P Q : Complex A} (f : P ⟶ Q) (T : Complex A)
    (n : ℤ) (z : Homogeneous Q T n) :
    (homPrecompose f T).f n z = (Cochain.ofHom f).comp z (zero_add n) := rfl

/-- 原変数を固定した A 線形 Hom 関手。 -/
def homFunctor (P : Complex A) : Complex A ⥤ Complex A where
  obj Q := homComplex A P Q
  map f := homPostcompose P f
  map_id Q := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact Cochain.comp_id z
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Cochain.ext
    intro p q hpq
    simp [homPostcompose, Cochain.comp_zero_cochain_v]
end SerrePositivity.DifferentialGraded
end

end HomFunctor

/-! ## Unit（旧 SerrePositivity/DifferentialGraded/Complexes/Unit.lean） -/

/-! # 単位からの射と閉次数零の元 -/

@[expose] public section Unit
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable {A : Type u} [CommRing A]

/-- 複体 K の次数零の cycle の A 部分加群。 -/
abbrev zeroCycles (K : Complex A) := LinearMap.ker (K.d 0 1).hom

/-- 閉次数零の元から単位複体を始域とする射を構成する。 -/
def unitFromCycle (K : Complex A) (c : zeroCycles K) : 𝟙_ (Complex A) ⟶ K :=
  mkHomFromSingle (ModuleCat.ofHom
    { toFun a := a • c.val
      map_add' a b := add_smul a b _
      map_smul' a b := mul_smul a b _ }) (by
    intro j hj
    obtain rfl : j = 1 := by simpa using hj.symm
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change (K.d 0 1).hom (a • c.val) = 0
    rw [map_smul, c.property, smul_zero])

/-- 単位からの射の次数零成分を 1 に評価する。 -/
def cycleFromUnit (K : Complex A) (f : 𝟙_ (Complex A) ⟶ K) : zeroCycles K :=
  ⟨f.f 0 ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv 1), by
    have hf := f.comm 0 1
    change f.f 0 ≫ K.d 0 1 =
      ((single (ModuleCat A) (.up ℤ) 0).obj (𝟙_ (ModuleCat A))).d 0 1 ≫ f.f 1 at hf
    rw [single_obj_d, zero_comp] at hf
    change (K.d 0 1).hom (f.f 0 _) = 0
    exact congr($(hf).hom ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv 1))⟩

/-- 構成後の評価は元の cycle を返す。 -/
@[simp]
lemma cycleFromUnit_unitFromCycle (K : Complex A) (c : zeroCycles K) :
    cycleFromUnit K (unitFromCycle K c) = c := by
  apply Subtype.ext
  change (unitFromCycle K c).f 0 (1 : A) = c.val
  dsimp only [unitFromCycle]
  rw [mkHomFromSingle_f]
  change (1 : A) • c.val = c.val
  exact one_smul A _

/-- 評価した cycle からの構成は元の射を返す。 -/
@[simp]
lemma unitFromCycle_cycleFromUnit (K : Complex A) (f : 𝟙_ (Complex A) ⟶ K) :
    unitFromCycle K (cycleFromUnit K f) = f := by
  apply from_single_hom_ext
  dsimp only [unitFromCycle]
  rw [mkHomFromSingle_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (show A from a) • f.f 0 (1 : A) = f.f 0 a
  simpa using ((f.f 0).hom.map_smul (show A from a) (1 : A)).symm

/-- Z⁰ の単位からの射と閉次数零の元は同値。 -/
def unitCycleEquiv (K : Complex A) : (𝟙_ (Complex A) ⟶ K) ≃ zeroCycles K where
  toFun := cycleFromUnit K
  invFun := unitFromCycle K
  left_inv := unitFromCycle_cycleFromUnit K
  right_inv := cycleFromUnit_unitFromCycle K
end SerrePositivity.DifferentialGraded

namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable {A : Type u} [CommRing A]

/-- 単位からの射を結ぶホモトピーと Hom 複体の −1 境界は同じ関係。 -/
lemma unit_homotopy_iff (K : Complex A) (f g : 𝟙_ (Complex A) ⟶ K) :
    Nonempty (Homotopy f g) ↔
      ∃ h : CochainComplex.HomComplex.Cochain (𝟙_ (Complex A)) K (-1),
        CochainComplex.HomComplex.Cochain.ofHom f =
          CochainComplex.HomComplex.δ (-1) 0 h + CochainComplex.HomComplex.Cochain.ofHom g := by
  constructor
  · rintro ⟨h⟩
    exact ⟨_, ((CochainComplex.HomComplex.Cochain.equivHomotopy f g) h).property⟩
  · rintro ⟨h, dh⟩
    exact ⟨(CochainComplex.HomComplex.Cochain.equivHomotopy f g).symm ⟨h, dh⟩⟩
end SerrePositivity.DifferentialGraded
end

end Unit

/-! ## GradedConjugationComposition（旧 SerrePositivity/DifferentialGraded/Complexes/GradedConjugationComposition.lean） -/

/-!
概要：次数を持つ互いに逆な cochain の中間対を、六項合成から消去する。
方針：全次数の成分を同じ中間添字で評価し、実際の分裂恒等式を合成する。
規約：シフトや閉射を仮定せず、全ての次数の等式を明示する。
使われ方：coherent bar の shift ブロック合成の厳密な照合。
-/

@[expose] public section GradedConjugationComposition
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable {R : Type u} [CommRing R] {K M N T P L : Complex R}

lemma cochainSixfold_cancel {s t r p q a b c : ℤ}
    (A : Cochain K M s) (f : Cochain M N p) (U : Cochain N T (-t))
    (V : Cochain T N t) (g : Cochain N P q) (B : Cochain P L (-r))
    (hUV : U.comp V (neg_add_cancel t) = Cochain.ofHom (𝟙 N))
    (ha : s + p - t = a) (hb : t + q - r = b) (hc : a + b = c) :
    ((A.comp f rfl).comp U (by omega : s + p + -t = a)).comp
        ((V.comp g rfl).comp B (by omega : t + q + -r = b)) hc =
      (A.comp (f.comp g rfl) rfl).comp B (by omega : s + (p + q) + -r = c) := by
  apply Cochain.ext
  intro i j hij
  rw [Cochain.comp_v _ _ hc i (i + a) j rfl (by omega)]
  rw [Cochain.comp_v _ _ _ i (i + s + p) (i + a) (by omega) (by omega)]
  rw [Cochain.comp_v _ _ _ (i + a) (i + s + p + q) j (by omega) (by omega)]
  rw [Cochain.comp_v A f rfl i (i + s) (i + s + p) rfl rfl]
  rw [Cochain.comp_v V g rfl (i + a) (i + s + p) (i + s + p + q)
    (by omega) rfl]
  rw [Cochain.comp_v _ B _ i (i + s + p + q) j (by omega) (by omega)]
  rw [Cochain.comp_v A _ rfl i (i + s) (i + s + p + q) rfl (by omega)]
  rw [Cochain.comp_v f g rfl (i + s) (i + s + p) (i + s + p + q) rfl rfl]
  have hm := Cochain.congr_v hUV (i + s + p) (i + s + p) (by omega)
  rw [Cochain.comp_v U V _ (i + s + p) (i + a) (i + s + p)
    (by omega) (by omega), Cochain.ofHom_v, HomologicalComplex.id_f] at hm
  have hcomp := congrArg (fun k : (N.X (i + s + p) ⟶ N.X (i + s + p)) =>
    A.v i (i + s) rfl ≫ f.v (i + s) (i + s + p) rfl ≫ k ≫
      g.v (i + s + p) (i + s + p + q) rfl ≫
      B.v (i + s + p + q) j (by omega)) hm
  simpa only [Category.assoc, Category.id_comp] using hcomp

end SerrePositivity.DifferentialGraded
end

end GradedConjugationComposition
