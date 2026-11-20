module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.Blowup
public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps

/-!
概要：KST §5 の Rees 代数の係数環に関する関手性。
方針：中心イデアルを保つ環準同型を多項式の係数ごとに適用する。
規約：通常の Rees 代数と次数付けを用い、平坦性は仮定しない。
使われ方：局所化との両立、一般スキーム上の貼り合わせ、古典的比較射。
-/

@[expose] public noncomputable section

universe u v w
namespace SerrePositivity.AlgebraicGeometry
open Polynomial
variable {R : Type u} {S : Type v} {T : Type w}
  [CommRing R] [CommRing S] [CommRing T]
  (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : I.map f ≤ J)

/--
概要：中心を保つ環準同型は各正整数冪の中心も保つ。
方針：イデアルの像と冪が可換することを使う。
規約：KST §5、指数零も含む。
使われ方：Rees 代数の係数に関する写像の定義。
-/
theorem map_pow_center_le (hf : I.map f ≤ J) (n : ℕ) : (I ^ n).map f ≤ J ^ n := by
  rw [Ideal.map_pow]
  exact pow_le_pow_left' hf n

/--
概要：中心を保つ環準同型が誘導する Rees 代数の環準同型。
方針：多項式の係数写像が各 Iⁿ を Jⁿ に送ることを確認する。
規約：KST §5、任意の可換環準同型に適用する。
使われ方：blowup の基底に関する比較と局所化。
-/
def reesMap : reesAlgebra I →+* reesAlgebra J where
  toFun p := ⟨p.1.map f, fun n => by
    rw [Polynomial.coeff_map]
    exact map_pow_center_le I J f hf n (Ideal.mem_map_of_mem f (p.2 n))⟩
  map_one' := Subtype.ext (Polynomial.map_one f)
  map_zero' := Subtype.ext (Polynomial.map_zero f)
  map_add' p q := Subtype.ext (Polynomial.map_add f)
  map_mul' p q := Subtype.ext (Polynomial.map_mul f)

/--
概要：Rees 代数の係数写像は元の多項式の係数写像と両立する。
方針：定義から従う。
規約：KST §5、下付きの中心を明示する。
使われ方：次数保存と合成の計算。
-/
@[simp] theorem reesMap_val (p : reesAlgebra I) :
    (reesMap I J f hf p).1 = p.1.map f := rfl

/--
概要：Rees 代数の係数写像は次数を保つ。
方針：単一次数の元を単項式と同定し、係数写像を適用する。
規約：KST §5、独自の次数構造は追加しない。
使われ方：Proj の反変関手へ渡す次数付き環準同型。
-/
def reesGradedMap : reesGrade I →+*ᵍ reesGrade J where
  __ := reesMap I J f hf
  map_mem {i p} hp := by
    apply (mem_reesGrade_iff J i _).mpr
    rw [reesMap_val, (mem_reesGrade_iff I i p).mp hp]
    simp

/--
概要：Rees 代数の係数写像は定数係数と両立する。
方針：定数多項式に係数写像を適用する。
規約：KST §5、基礎環上の構造射の比較に使う。
使われ方：blowup の比較射の基底両立性。
-/
@[simp] theorem reesMap_base (r : R) :
    reesMap I J f hf (algebraMap R (reesAlgebra I) r) =
      algebraMap S (reesAlgebra J) (f r) := by
  apply Subtype.ext
  exact Polynomial.map_C f

/--
概要：Rees 代数の係数写像は次数一の中心元と両立する。
方針：単項式の係数写像を計算する。
規約：KST §5、像の中心への所属を明示する。
使われ方：標準チャートの比較。
-/
@[simp] theorem reesMap_degreeOne (a : I) :
    reesMap I J f hf (reesDegreeOne I a) =
      reesDegreeOne J ⟨f a.1, hf (Ideal.mem_map_of_mem f a.2)⟩ := by
  apply Subtype.ext
  exact Polynomial.map_monomial f

/--
概要：恒等係数写像が誘導する Rees 代数の写像は恒等射。
方針：多項式への包含の単射性で判定する。
規約：KST §5、中心の同定は恒等写像による像。
使われ方：貼り合わせの恒等射条件。
-/
@[simp] theorem reesMap_id : reesMap I I (RingHom.id R) (by simp) = RingHom.id _ := by
  ext p : 1
  apply Subtype.ext
  exact Polynomial.map_id

/--
概要：Rees 代数の係数写像は合成を保つ。
方針：多項式への包含を通して係数写像の合成を計算する。
規約：KST §5、中心を保つ二つの写像の合成を扱う。
使われ方：一般スキームへの貼り合わせの三重交叉条件。
-/
theorem reesMap_comp (K : Ideal T) (g : S →+* T) (hg : J.map g ≤ K) :
    (reesMap J K g hg).comp (reesMap I J f hf) =
      reesMap I K (g.comp f) (by
        rw [← Ideal.map_map]
        exact (Ideal.map_mono hf).trans hg) := by
  ext p : 1
  apply Subtype.ext
  exact Polynomial.map_map f g p.1

/--
概要：全射な係数環準同型は、像の中心の Rees 代数にも全射を誘導する。
方針：有限個の多項式係数を各 Iⁿ の中で持ち上げ、単項式の和を取る。
規約：KST §5、中心は像イデアル。平坦性は仮定しない。
使われ方：商環への比較と通常の blowup からの閉埋め込みの構成。
-/
theorem reesMap_surjective (hfs : Function.Surjective f) :
    Function.Surjective (reesMap I (I.map f) f le_rfl) := by
  classical
  intro p
  have hlift (n : ℕ) : ∃ r : R, r ∈ I ^ n ∧ f r = p.1.coeff n := by
    apply (Ideal.mem_map_iff_of_surjective f hfs).mp
    rw [Ideal.map_pow]
    exact p.2 n
  choose c hc hfc using hlift
  let q : reesAlgebra I := ∑ n ∈ p.1.support, reesMonomial I n ⟨c n, hc n⟩
  refine ⟨q, Subtype.ext ?_⟩
  rw [reesMap_val]
  change (Polynomial.mapRingHom f) ((reesAlgebra I).val q) = p.1
  dsimp only [q]
  rw [map_sum]
  simp only [map_sum, reesMonomial, Subalgebra.val_apply, Polynomial.coe_mapRingHom,
    Polynomial.map_monomial, hfc]
  exact p.1.as_sum_support.symm

/--
概要：単射な係数環準同型は Rees 代数にも単射を誘導する。
方針：多項式の係数ごとの単射性を用いる。
規約：KST §5、像の中心への包含以外の仮定はない。
使われ方：局所化との比較と基底環の同型による移送。
-/
theorem reesMap_injective (hfi : Function.Injective f) :
    Function.Injective (reesMap I J f hf) := by
  intro p q hpq
  apply Subtype.ext
  exact Polynomial.map_injective f hfi (congrArg Subtype.val hpq)

/--
概要：像の中心の Rees 代数の irrelevant ideal は、元の irrelevant ideal の像に含まれる。
方針：各正次数で、係数を像イデアルの生成元から線形に拡張する。
規約：KST §5、係数環準同型の全射性や平坦性は不要。
使われ方：Proj の反変関手による通常の blowup の基底比較射。
-/
theorem reesGradedMap_irrelevant_le :
    HomogeneousIdeal.irrelevant (reesGrade (I.map f)) ≤
      (HomogeneousIdeal.irrelevant (reesGrade I)).map
        (reesGradedMap I (I.map f) f le_rfl) := by
  apply (HomogeneousIdeal.irrelevant_le _).mpr
  intro n hn p hp
  let Q := ((HomogeneousIdeal.irrelevant (reesGrade I)).map
    (reesGradedMap I (I.map f) f le_rfl)).toIdeal
  let T : Submodule S S :=
    ((Q.restrictScalars S).map (reesAlgebra (I.map f)).val.toLinearMap).comap (monomial n)
  have hmap : (I ^ n).map f ≤ T := by
    change Submodule.span S (f '' ((I ^ n : Ideal R) : Set R)) ≤ T
    apply Submodule.span_le.mpr
    rintro _ ⟨r, hr, rfl⟩
    refine ⟨reesMap I (I.map f) f le_rfl (reesMonomial I n ⟨r, hr⟩), ?_, ?_⟩
    · exact Ideal.mem_map_of_mem _
        (HomogeneousIdeal.mem_irrelevant_of_mem _ hn (reesMonomial_mem I n ⟨r, hr⟩))
    · change (monomial n r).map f = monomial n (f r)
      exact Polynomial.map_monomial f
  have hcoeff : p.1.coeff n ∈ (I ^ n).map f := by
    rw [Ideal.map_pow]
    exact p.2 n
  obtain ⟨q, hq, heq⟩ := hmap hcoeff
  have hqp : q = p := Subtype.ext (heq.trans ((mem_reesGrade_iff _ _ _).mp hp).symm)
  exact hqp ▸ hq

/--
概要：恒等係数写像の Rees 次数付き写像は恒等射。
方針：基になる 環準同型の恒等性を次数付き写像へ移す。
規約：KST §5、次数付けは既存の Rees 次数付け。
使われ方：アフィン開集合での比較の恒等射条件。
-/
@[simp] theorem reesGradedMap_id :
    reesGradedMap I I (RingHom.id R) (by simp) = GradedRingHom.id (reesGrade I) := by
  apply GradedRingHom.ext
  intro p
  exact DFunLike.congr_fun (reesMap_id I) p

/--
概要：Rees の次数付き係数写像は合成を保つ。
方針：基になる 環準同型の合成則を次数付き写像へ移す。
規約：KST §5、三つの中心と二つの中心を保つ準同型を明示する。
使われ方：blowup のチャート比較の三重交叉条件。
-/
theorem reesGradedMap_comp (K : Ideal T) (g : S →+* T) (hg : J.map g ≤ K) :
    (reesGradedMap J K g hg).comp (reesGradedMap I J f hf) =
      reesGradedMap I K (g.comp f) (by
        rw [← Ideal.map_map]
        exact (Ideal.map_mono hf).trans hg) := by
  apply GradedRingHom.ext
  intro p
  exact DFunLike.congr_fun (reesMap_comp I J f hf K g hg) p

/--
概要：像中心を同定した表示でも irrelevant ideal の包含が成立する。
方針：中心の等式に沿って像中心の場合の証明を移送する。
規約：KST §5、中心の等式だけを仮定する。
使われ方：アフィン開集合のイデアル切断の中心を保つ比較。
-/
theorem reesGradedMap_irrelevant_le_of_eq (hJ : I.map f = J) :
    HomogeneousIdeal.irrelevant (reesGrade J) ≤
      (HomogeneousIdeal.irrelevant (reesGrade I)).map
        (reesGradedMap I J f hJ.le) := by
  subst J
  exact reesGradedMap_irrelevant_le I f

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
