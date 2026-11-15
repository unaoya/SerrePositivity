module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardHomNormalizedTop
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DoldKanIso
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWPreservation

/-!
# 指定 Dold–Kan Hom 同型の射影による全次数評価

概要：指定 DK 同型の像から元の標準 Hom の正次数成分を回収する。
方針：同じ随伴の余単位則と Moore 射影の自然性を合成する。
規約：Γ、随伴、正規化同型、射影は既存の指定されたものを使う。
使われ方：HA 1.2.4、Kerodon 2.5（Tag 00ND）の G10 の全単体の合成照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory DifferentialGraded AlgebraicTopology
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories
open DifferentialGradedCategories
open scoped Simplicial
variable {R : Type u} [CommRing R]

/-- 概要：指定 Hom 随伴の像を射影と余単位で全次数に評価する。
方針：射影の自然性と随伴 Hom の逆写像の式。
規約：同じ射影の因子分解。使われ方：HA 1.2.4 の指定 DK 像の評価。 -/
theorem doldKanHomEquiv_projected_eval (W : SimplicialObject (ModuleCat R))
    (K : ChainComplex (ModuleCat R) ℕ)
    (f : (normalizedMooreComplex (ModuleCat R)).obj W ⟶ K) (n : ℕ) :
    (((Abelian.DoldKan.equivalence : SimplicialObject (ModuleCat R) ≌
      ChainComplex (ModuleCat R) ℕ).toAdjunction.homEquiv W K) f).app (Opposite.op ⦋n⦌) ≫
      (DoldKan.PInftyToNormalizedMooreComplex (Abelian.DoldKan.Γ.obj K)).f n ≫
      (Abelian.DoldKan.equivalence.counitIso.hom.app K).f n =
    (DoldKan.PInftyToNormalizedMooreComplex W).f n ≫ f.f n := by
  let e : SimplicialObject (ModuleCat R) ≌ ChainComplex (ModuleCat R) ℕ :=
    Abelian.DoldKan.equivalence
  let g := e.toAdjunction.homEquiv W K f
  have hg : (normalizedMooreComplex (ModuleCat R)).map g ≫ e.counitIso.hom.app K = f :=
    (e.toAdjunction.homEquiv W K).symm_apply_apply f
  have hn := congrArg (fun t => t ≫ e.counitIso.hom.app K)
    (DoldKan.PInftyToNormalizedMooreComplex_naturality g)
  change NormalizedMooreComplex.map g ≫ e.counitIso.hom.app K = f at hg
  simp only [Category.assoc] at hn
  rw [hg] at hn
  have h := congrArg (fun t => t.f n) hn
  simp only [HomologicalComplex.comp_f] at h ⊢
  exact h

variable {D : Type v} [DGCategory R D]

/-- 概要：実標準 DK 同型の像の正次数評価は元の最上位成分である。
方針：同じ随伴の評価式を正規化同型と既存の射影評価に接続する。
規約：正次数を全て扱う。使われ方：HA 1.2.4 の実豊穣合成との成分照合。 -/
theorem standardDoldKanModuleIso_positive_projected_eval (x y : D) (n : ℕ) :
    (standardDoldKanModuleIso (R := R) x y).hom.app (Opposite.op ⦋n + 1⦌) ≫
      (DoldKan.PInftyToNormalizedMooreComplex
        (doldKanHomModule (R := R) x y)).f (n + 1) ≫
      (Abelian.DoldKan.equivalence.counitIso.hom.app
        (connectiveHomComplex (R := R) x y)).f (n + 1) ≫
      (connectiveHomComplex_positiveIso (R := R) x y n).hom =
    ModuleCat.ofHom (standardTopEval (R := R) x y (n + 1)) := by
  have h := doldKanHomEquiv_projected_eval (standardModule (R := R) x y)
    (connectiveHomComplex (R := R) x y) (standardNormalizationIso (R := R) x y).hom (n + 1)
  change (standardDoldKanModuleIso (R := R) x y).hom.app (Opposite.op ⦋n + 1⦌) ≫
      _ ≫ _ = _ at h
  have he : (standardNormalizationIso (R := R) x y).hom.f (n + 1) ≫
      (connectiveHomComplex_positiveIso (R := R) x y n).hom =
      standardMooreTopMap (R := R) x y n := by
    change (standardMoorePositiveIso (R := R) x y n).hom ≫
      (connectiveHomComplex_positiveIso (R := R) x y n).inv ≫
      (connectiveHomComplex_positiveIso (R := R) x y n).hom = _
    rw [Iso.inv_hom_id, Category.comp_id]
    rfl
  calc
    _ = ((DoldKan.PInftyToNormalizedMooreComplex
        (standardModule (R := R) x y)).f (n + 1) ≫
        (standardNormalizationIso (R := R) x y).hom.f (n + 1)) ≫
        (connectiveHomComplex_positiveIso (R := R) x y n).hom := by
      simp only [Category.assoc]
      exact congrArg
        (fun t => t ≫ (connectiveHomComplex_positiveIso (R := R) x y n).hom) h
    _ = _ := by rw [Category.assoc, he, standardMooreTopMap_projection]

/-- 概要：実標準 AW 合成の DK 像を評価すると同じ切断点の和となる。
方針：指定 DK 評価公式と既存の AW 成分定義を合成する。
規約：後の射 g を先に置く。使われ方：HA 1.2.4 の実豊穣合成の照合。 -/
theorem standardDoldKanAW_positive_projected_eval {x y z : D} {n : ℕ}
    (g : StandardSimplex R y z (n + 1)) (f : StandardSimplex R x y (n + 1)) :
    ((standardDoldKanModuleIso (R := R) x z).hom.app (Opposite.op ⦋n + 1⦌) ≫
      (DoldKan.PInftyToNormalizedMooreComplex
        (doldKanHomModule (R := R) x z)).f (n + 1) ≫
      (Abelian.DoldKan.equivalence.counitIso.hom.app
        (connectiveHomComplex (R := R) x z)).f (n + 1) ≫
      (connectiveHomComplex_positiveIso (R := R) x z n).hom) (standardAW g f) =
    ∑ j : (Finset.univ : Finset (Fin (n + 2))),
      awTerm g.val f.val Finset.univ j (-(n + 1 : ℤ)) (by simp) := by
  have h := ConcreteCategory.congr_hom
    (standardDoldKanModuleIso_positive_projected_eval (R := R) x z n) (standardAW g f)
  exact h.trans (by rfl)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
