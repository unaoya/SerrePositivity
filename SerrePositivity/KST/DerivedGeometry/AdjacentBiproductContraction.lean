module

public import SerrePositivity.KST.DerivedGeometry.ContractibleInjectiveEnvelope
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-!
概要：隣接双積複体の縮約と非輪状性。
方針：第一成分を一つ前の第二成分へ送るホモトピーを構成する。
規約：任意の対象族。有界性も各項の injectivity も縮約自体には不要。
使われ方：Stacks Lemma 19.12.5 (079N)、TT §3・§8、Toën §3.2 の非有界分解の構成部品。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type*} [Category* C] [Abelian C] (I : ℤ → C)

/--
概要：隣接双積複体の恒等写像は零ホモトピーを持つ。
方針：第一成分から一つ前の第二成分への射を使い、二つの射影の和が恒等であることを使う。
規約：実際の縮約を成分で構成する。
使われ方：Stacks Lemma 19.12.5、TT §3 の contractible な埋め込み先。
-/
def adjacentBiproductContraction : Homotopy (𝟙 (adjacentBiproductComplex I)) 0 where
  hom i j := if h : j + 1 = i then
      biprod.fst ≫ eqToHom (congrArg I h.symm) ≫ biprod.inr else 0
  zero i j h := dite_eq_right (by exact h)
  comm i := by
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i by change (i - 1) + 1 = i; omega)]
    simp [adjacentBiproductComplex, Category.assoc, add_comm, biprod.total]

/--
概要：隣接双積複体は非輪状。
方針：縮約が恒等コホモロジー写像を零にすることを使う。
規約：全ての整数次数。
使われ方：Stacks Lemma 19.12.5、Toën §3.2 の準同型の比較。
-/
lemma adjacentBiproductComplex_acyclic : (adjacentBiproductComplex I).Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
  simpa using (adjacentBiproductContraction I).homologyMap_eq n

/--
概要：隣接双積複体は K-injective。
方針：縮約を任意の射へ前合成して零ホモトピーを得る。
規約：各項 injective からの推論を使わない。
使われ方：Stacks Lemma 19.12.5、TT §3 の非有界分解の縮約。
-/
instance adjacentBiproductComplex_isKInjective : (adjacentBiproductComplex I).IsKInjective where
  nonempty_homotopy_zero f _ := ⟨by simpa using (adjacentBiproductContraction I).compLeft f⟩

end SerrePositivity.KST.DerivedGeometry
