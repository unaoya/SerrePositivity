module

public import SerrePositivity.KST.Spectra.LinearGroupCofaces
public import SerrePositivity.KST.Spectra.RationalGroupCohomology

/-!
概要：線形な余単体群 cochain の交代余面複体と Mathlib の非斉次 cochain 複体の実際の同型。
方針：各余面の式から微分を照合し、各次数の恒等同型を複体の同型に束ねる。
規約：この比較は代数的な cochain 複体の主張であり Tot のホモトピー群をまだ計算しない。
使われ方：Goerss–Jardine VIII §2。有限群の有理 cochain の消滅の入力を余単体構造へ接続する。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.LinearGroupCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k G : Type u} [CommRing k] [Group G]

/-- 概要：表現の非斉次余単体 cochain の交代微分は標準の非斉次群 cochain 微分。
方針：余面の交代和の座標式を比較し、整数符号を係数環の符号へ移す。
規約：各次数の係数加群の恒等射で同定する。
使われ方：Goerss–Jardine VIII §2。Mathlib の bar cochain 複体との微分の整合性。 -/
lemma objD_eq_inhomogeneous (A : Rep.{u} k G) (n : ℕ) :
    AlgebraicTopology.AlternatingCofaceMapComplex.objD (obj ((Rep.RepToAction k G).obj A)) n =
      inhomogeneousCochains.d A n := by
  ext x
  change ((Fin n → G) → A) at x
  funext s
  rw [alternating_d_apply]
  change A.ρ (s 0) (x (Fin.tail s)) +
      ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j.val + 1) • x (Fin.contractNth j (· * ·) s) =
    A.ρ (s 0) (x (Fin.tail s)) +
      ∑ j : Fin (n + 1), (-1 : k) ^ (j.val + 1) • x (Fin.contractNth j (· * ·) s)
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [← Int.cast_smul_eq_zsmul k]
  simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- 概要：表現の線形な非斉次余単体図式の交代余面複体。
方針：標準の交代余面複体の関手を適用する。
規約：複体の次数は自然数で、微分は次数を一つ上げる。
使われ方：Goerss–Jardine VIII §2。群コホモロジーの比較の始域。 -/
def complex (A : Rep.{u} k G) : CochainComplex (ModuleCat.{u} k) ℕ :=
  AlgebraicTopology.AlternatingCofaceMapComplex.obj (obj ((Rep.RepToAction k G).obj A))

/-- 概要：余単体 cochain の交代余面複体は標準の非斉次群 cochain 複体と同型。
方針：各次数の恒等同型と微分の一致を使う。
規約：実際の cochain complex の同型。
使われ方：Goerss–Jardine VIII §2。既存の群コホモロジーの計算への比較。 -/
def inhomogeneousIso (A : Rep.{u} k G) : complex A ≅ groupCohomology.inhomogeneousCochains A :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
    rintro i j (h : i + 1 = j)
    subst h
    simpa only [complex, AlgebraicTopology.AlternatingCofaceMapComplex.obj,
      CochainComplex.of_d, groupCohomology.inhomogeneousCochains.d_def,
      Iso.refl_hom, Category.comp_id, Category.id_comp] using (objD_eq_inhomogeneous A i).symm)

/-- 概要：線形な余単体 cochain の複体のコホモロジーは群コホモロジーと同型。
方針：非斉次複体の実際の同型に homology 関手を適用する。
規約：零次数を含む全自然数次数で成立する。
使われ方：Goerss–Jardine VIII §2。有理平均化の消滅を交代余面複体へ移す。 -/
def cohomologyIso (A : Rep.{u} k G) (n : ℕ) :
    (complex A).homology n ≅ groupCohomology A n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℕ) n).mapIso
    (inhomogeneousIso A)

end

end SerrePositivity.KST.Spectra.LinearGroupCochains
