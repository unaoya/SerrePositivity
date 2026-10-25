module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarLowerIndex
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoproductIndexEmbedding
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarTopExact

/-!
概要：上界以下の部分圏のホモロジー bar は、全体へ次数ごと単射に入る。
方針：単体ラベルの単射性を、実直和包含の分裂射影へ渡す。
規約：加群の係数は同じ始点のまま。
使われ方：持ち上げた有限 cycle の閉性を部分圏へ反映する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits Opposite SSet AlgebraicTopology
open scoped Simplicial
variable (R : Type u) [CommRing R] {J : Type u} [PartialOrder J]
  (F : J ⥤ ModuleCat.{u} R)

abbrev dgHomologyBarLowerDiagram (b : J) : Set.Iic b ⥤ ModuleCat R :=
  dgHomologyBarLowerInclusion b ⋙ F

def dgHomologyBarLowerMap (b : J) :
    dgHomologyBarComplex R (dgHomologyBarLowerDiagram R F b) ⟶ dgHomologyBarComplex R F :=
  AlternatingFaceMapComplex.map (dgHomologyBarIndexMap R F (dgHomologyBarLowerInclusion b))

lemma dgHomologyBarLowerMap_injective (b : J) (n : ℕ) :
    Function.Injective ((dgHomologyBarLowerMap R F b).f n) :=
  dgBarCoproductIndexInclusion_injective R
    (fun s : (nerve (Set.Iic b)) _⦋n⦌ => s ⋙ dgHomologyBarLowerInclusion b)
    (dgHomologyBarFamily R F (op ⦋n⦌))
    (dgHomologyBarLowerInclusion_simplex_injective b n)

lemma dgHomologyBarLowerMap_lift_ι {n : ℕ} (s : (nerve J) _⦋n⦌) (b : J)
    (hb : s.obj (Fin.last n) ≤ b) :
    Sigma.ι (dgHomologyBarFamily R (dgHomologyBarLowerDiagram R F b) (op ⦋n⦌))
      (dgHomologyBarLiftSimplex s b hb) ≫ (dgHomologyBarLowerMap R F b).f n =
    Sigma.ι (dgHomologyBarFamily R F (op ⦋n⦌)) s := by
  erw [dgHomologyBarIndexMap_ι]
  have h := Sigma.eqToHom_comp_ι (dgHomologyBarFamily R F (op ⦋n⦌))
    (dgHomologyBarLiftSimplex_comp s b hb)
  simpa only [eqToHom_refl, Category.id_comp] using! h

end SerrePositivity.InfinityCategories
