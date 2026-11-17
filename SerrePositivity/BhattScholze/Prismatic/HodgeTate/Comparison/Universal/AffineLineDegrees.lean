module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineLineCriterion
public import SerrePositivity.CommutativeAlgebra.DeRham.PolynomialDeRhamCompletionUnit

/-!
# 元の一変数の形式と全複体の次数の支え

## 概要
元の二次数形式模型の微分は零で、一変数の形式は一次を超えると零になる。

## 方針
元の直和の射影の可換式と恒等式、元の有限変数の外冪の零性を使う。

## 規約
HT比較の入力は明示し、ここで一般の比較を証明したとは数えない。

## 使われ方
HT03の特定の結晶被覆上の比較と合わせ、元のηの他の次数を検査する。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded SerrePositivity.DeRham
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A)

/-- 元の二次数の形式模型の、元の微分は全て零。 -/
theorem affineLineFormal_d_zero (i j : ℤ) : (affineLineFormalModel P).d i j = 0 := by
  let R := affineAlgebra P 1
  let K := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
    (ModuleCat.of R (affineForms P 1 0))
  let L := (CochainComplex.singleFunctor (ModuleCat.{u} R) 1).obj
    (ModuleCat.of R (affineForms P 1 1))
  let F := K ⊞ L
  have hf : F.d i j ≫ (biprod.fst : F ⟶ K).f j = 0 := by
    rw [← (biprod.fst : F ⟶ K).comm]
    change _ ≫ 0 = 0
    simp only [comp_zero]
  have hs : F.d i j ≫ (biprod.snd : F ⟶ L).f j = 0 := by
    rw [← (biprod.snd : F ⟶ L).comm]
    change _ ≫ 0 = 0
    simp only [comp_zero]
  have ht := congrArg (fun t : F ⟶ F => t.f j)
    (show (biprod.fst : F ⟶ K) ≫ biprod.inl + (biprod.snd : F ⟶ L) ≫ biprod.inr = 𝟙 F
      from biprod.total)
  simp only [HomologicalComplex.add_f_apply, HomologicalComplex.comp_f, HomologicalComplex.id_f] at ht
  change F.d i j = 0
  rw [← Category.comp_id (F.d i j), ← ht, Preadditive.comp_add, ← Category.assoc,
    ← Category.assoc, hf, hs, zero_comp, zero_comp, zero_add]

/-- 元の一変数の完備形式は、一次を超えると零。 -/
theorem affineLineForms_isZero (i : ℕ) (hi : 1 < i) :
    IsZero (ModuleCat.of (affineAlgebra P 1) (affineForms P 1 i)) := by
  let k := A ⧸ P.ideal
  let T := formVars.{u} 1
  haveI : Subsingleton (forms k T i) := ModuleCat.subsingleton_of_isZero
    (forms_isZero_of_card_lt k T i (by simpa [T, formVars] using hi))
  apply ModuleCat.isZero_iff_subsingleton.mpr
  change Subsingleton (completedPoly k T p ⊗[Poly k T] forms k T i)
  infer_instance

variable (hP : IsBoundedPrism P)

/-- 元の一変数の標準HT写像が同型なら、元の指定全複体の一次を超えるホモロジーは零。 -/
theorem affineHTTotal_homology_high_of_HT (h : HodgeTateIsoStatement P hP 1)
    (i : ℕ) (hi : 1 < i) : IsZero ((affineHTTotalComplex P hP 1).homology (i : ℤ)) := by
  haveI : Subsingleton (affineForms P 1 i) := ModuleCat.subsingleton_of_isZero (affineLineForms_isZero P i hi)
  have hb := (affineHTTotalMap_bijective_iff P hP 1 i).mpr
    ((hodgeTateIsoStatement_iff_affineHTMap_bijective P hP 1).mp h i)
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, rfl⟩ := hb.2 x
  obtain ⟨b, rfl⟩ := hb.2 y
  exact congrArg (affineHTTotalMap P hP 1 i) (Subsingleton.elim a b)

/-- 元の指定HT全複体は、元の非負余鎖複体の零延長により負次数ではホモロジーを持たない。 -/
theorem affineHTTotal_homology_negative (r : ℕ) (i : ℤ) (hi : i < 0) :
    IsZero ((affineHTTotalComplex P hP r).homology i) := by
  let K := affineHTExtendedComplex P hP r
  have hz : IsZero (K.X i) := (affineHTComplex P hP r).isZero_extend_X
    ComplexShape.embeddingUpNat i (fun n hn => by change (n : ℤ) = i at hn; omega)
  have hh : IsZero (K.homology i) := (HomologicalComplex.exactAt_iff_isZero_homology K i).mp
    (ShortComplex.exact_of_isZero_X₂ _ hz)
  exact hh.of_iso ((homologyFunctor _ (.up ℤ) i).mapIso (affineHTTotalIso P hP r))

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
