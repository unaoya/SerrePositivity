module

public import SerrePositivity.HomologicalAlgebra.ConeLES

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

/-!
# cone 長完全列の自然性

概要：可換正方形が cone の連結写像と可換することを、複体のホモロジーで表す。
方針：ホモトピー圏の三角形の射の自然性を、ホモロジー比較同型で移す。
規約：元の射の正方形は厳密可換。スペクトル系列を使わない。
使われ方：KST Lemma 4.9・4.10 の冪遷移に沿う長完全列。
-/

universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R : Type u} [CommRing R]

/-- 概要：cone の連結写像は可換正方形に自然。
方針：三角形の射の自然性と Cone.e の自然性を合成する。
規約：次数の等式は明示する。使われ方：KST Lemma 4.10 の冪核への自然な射。 -/
theorem cone_connecting_naturality
    {K L K' L' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : K ⟶ L) (g : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : f ≫ b = a ≫ g) (i j : ℤ) (hij : i + 1 = j) :
    homologyMap (CochainComplex.mappingCone.map f g a b h) i ≫ Cone.δ g i j hij =
      Cone.δ f i j hij ≫ homologyMap a j := by
  let Q := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
  let φ := Q.mapTriangle.map (CochainComplex.mappingCone.triangleMap f g a b h)
  have hn := (Cone.H₀ (R := R)).homologySequenceδ_naturality φ i j hij
  change (HomotopyCategory.homologyFunctor _ _ i).map
      (Q.map (CochainComplex.mappingCone.map f g a b h)) ≫ _ =
    _ ≫ (HomotopyCategory.homologyFunctor _ _ j).map (Q.map a) at hn
  apply (cancel_epi (Cone.e i (CochainComplex.mappingCone f)).hom).mp
  rw [← Category.assoc, ← Cone.e_naturality i
      (CochainComplex.mappingCone.map f g a b h),
    Category.assoc, ← Cone.δ_square g i j hij,
    ← Category.assoc, hn, Category.assoc, Cone.e_naturality j a,
    ← Category.assoc, Cone.δ_square f i j hij, Category.assoc]

end SerrePositivity.KST.ProExcision
