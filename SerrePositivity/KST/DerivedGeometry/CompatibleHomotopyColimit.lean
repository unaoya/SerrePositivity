module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.Homotopy

/-!
概要：余極限上で互換な零ホモトピーの成分を貼り合わせる。
方針：評価関手の余極限保存と余極限の普遍性で各成分を構成する。
規約：添字の有向性を必要とせず、零ホモトピーの互換性は明示的な等式とする。
使われ方：Stacks Lemma 19.12.3 (079L)、TT §3・§8、Toën §3.2 の超限列の極限段階。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type*} [Category* C] [Abelian C]
  {J : Type*} [Category* J] {F : J ⥤ CochainComplex C ℤ}
  (c : Cocone F) (hc : IsColimit c) {I : CochainComplex C ℤ}
  (f : c.pt ⟶ I) (h : ∀ a, Homotopy (c.ι.app a ≫ f) 0)
  (hh : ∀ {a b} (u : a ⟶ b) i j, (F.map u).f i ≫ (h b).hom i j = (h a).hom i j)
  [∀ i, PreservesColimit F (HomologicalComplex.eval C (.up ℤ) i)]

include hc hh

/--
概要：互換な零ホモトピーの余極限は元の射の零ホモトピーとなる。
方針：各次数で評価した余極限の射を構成し、零ホモトピーの等式を余極限の脚で検証する。
規約：各脚への制限は元の零ホモトピーの全成分に一致する。
使われ方：Stacks 19.12.3、TT §3 の連続超限列の互換性。
-/
lemma exists_colimit_compatible_homotopy :
    ∃ k : Homotopy f 0, ∀ a i j, (c.ι.app a).f i ≫ k.hom i j = (h a).hom i j := by
  let D (i j : ℤ) : Cocone (F ⋙ HomologicalComplex.eval C (.up ℤ) i) :=
    { pt := I.X j
      ι := { app a := (h a).hom i j
             naturality a b u := by simpa using hh u i j } }
  let L (i : ℤ) := isColimitOfPreserves (HomologicalComplex.eval C (.up ℤ) i) hc
  let v (i j : ℤ) := (L i).desc (D i j)
  have hv (a : J) (i j : ℤ) : (c.ι.app a).f i ≫ v i j = (h a).hom i j :=
    (L i).fac (D i j) a
  have hz (i j : ℤ) (hij : ¬ (ComplexShape.up ℤ).Rel j i) : v i j = 0 := by
    apply (L i).hom_ext
    intro a
    change (c.ι.app a).f i ≫ v i j = (c.ι.app a).f i ≫ 0
    rw [hv, (h a).zero i j hij, comp_zero]
  have he : Homotopy.nullHomotopicMap v = f := by
    apply hc.hom_ext
    intro a
    rw [Homotopy.comp_nullHomotopicMap]
    have hv' : (fun i j => (c.ι.app a).f i ≫ v i j) = (h a).hom := by
      funext i j
      exact hv a i j
    rw [hv']
    simpa using (h a).sub_eq_nullHomotopicMap.symm
  let k : Homotopy f 0 :=
    { hom := v
      zero := hz
      comm i := by simpa only [Homotopy.nullHomotopy, he] using (Homotopy.nullHomotopy v hz).comm i }
  refine ⟨k, ?_⟩
  intro a i j
  exact hv a i j

end SerrePositivity.KST.DerivedGeometry
