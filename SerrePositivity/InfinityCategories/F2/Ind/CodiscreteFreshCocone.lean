module

public import SerrePositivity.InfinityCategories.F2.Ind.CodiscreteConeLabels
public import SerrePositivity.InfinityCategories.F2.Ind.SmallVerticesFreshLabel
public import SerrePositivity.InfinityCategories.F2.Filtered.FilteredInfinity
public import SerrePositivity.InfinityCategories.Core.Cocone

/-!
概要：ラベル付き積の小さい図式に、元の頂点に現れない頂点を持つ同じ積内の余錐を作る。
方針：元の底内の余錐に指定した新しい頂点ラベルの延長を組み合わせる。
規約：元の図式への制限を厳密に保つ。単射な錐写像の結論は別工程。
使われ方：終頂点を持つ小さい部分複体への拡大。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {K C : SSet.{u}} {T : Type u}

/-- 元の底の余錐と指定した頂点ラベルを同じ積内の余錐へ組み合わせる。 -/
def codiscreteProductCocone (p : K ⟶ C ⊗ nerve (Codiscrete T))
    (c : JoinCocone (p ≫ fst C (nerve (Codiscrete T)))) (a : T) : JoinCocone p :=
  ⟨lift c.val (codiscreteConeLabelMap (p ≫ snd C (nerve (Codiscrete T))) a), by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst]
      exact c.property
    · rw [Category.assoc, lift_snd]
      exact codiscreteConeLabelMap_inl _ _⟩

/-- 同じ積の余錐の第二成分は、指定した同じラベルの錐延長。 -/
lemma codiscreteProductCocone_snd (p : K ⟶ C ⊗ nerve (Codiscrete T))
    (c : JoinCocone (p ≫ fst C (nerve (Codiscrete T)))) (a : T) :
    (codiscreteProductCocone p c a).val ≫ snd C (nerve (Codiscrete T)) =
      codiscreteConeLabelMap (p ≫ snd C (nerve (Codiscrete T))) a := lift_snd _ _

/-- 同じ積の余錐の右頂点のラベルは指定した同じラベル。 -/
lemma codiscreteProductCocone_apex (p : K ⟶ C ⊗ nerve (Codiscrete T))
    (c : JoinCocone (p ≫ fst C (nerve (Codiscrete T)))) (a : T) :
    joinInr K Δ[0] ≫ (codiscreteProductCocone p c a).val ≫
      snd C (nerve (Codiscrete T)) = SSet.const (nerveVertex (Codiscrete.mk a)) := by
  rw [codiscreteProductCocone_snd, codiscreteConeLabelMap_inr]

/-- 未使用のラベルを持つ同じ余錐の頂点は、元の全ての頂点の像と異なる。 -/
lemma codiscreteProductCocone_fresh (p : K ⟶ C ⊗ nerve (Codiscrete T))
    (c : JoinCocone (p ≫ fst C (nerve (Codiscrete T)))) (a : T)
    (ha : ∀ x : K _⦋0⦌, (nerveEquiv ((p ≫ snd C (nerve (Codiscrete T))).app _ x)).as ≠ a) :
    ∀ x : K _⦋0⦌, p.app _ x ≠ (codiscreteProductCocone p c a).vertex := by
  have hv : (snd C (nerve (Codiscrete T))).app _ (codiscreteProductCocone p c a).vertex =
      nerveVertex (Codiscrete.mk a) := by
    rw [JoinCocone.vertex_eq, ← SSet.yonedaEquiv_comp, Category.assoc,
      codiscreteProductCocone_apex]
    rfl
  intro x hx
  apply ha x
  have h := congrArg (fun s => (nerveEquiv
    ((snd C (nerve (Codiscrete T))).app (Opposite.op ⦋0⦌) s)).as) hx
  rw [hv] at h
  exact h

/-- κ-filtered な元の底と十分大きいラベル集合は、元の小さい図式に新しい頂点の余錐を与える。 -/
lemma exists_fresh_codiscreteProductCocone {κ : Cardinal.{u}} [Quasicategory C]
    [IsKappaFiltered κ C] (hK : IsKappaSmall κ K) (hT : κ ≤ Cardinal.mk T)
    (p : K ⟶ C ⊗ nerve (Codiscrete T)) :
    ∃ d : JoinCocone p, ∀ x : K _⦋0⦌, p.app _ x ≠ d.vertex := by
  obtain ⟨c⟩ := IsKappaFiltered.cocone_nonempty hK (p ≫ fst C (nerve (Codiscrete T)))
  obtain ⟨a, ha⟩ := exists_fresh_vertex_label hK hT
    (fun x => (nerveEquiv ((p ≫ snd C (nerve (Codiscrete T))).app _ x)).as)
  exact ⟨codiscreteProductCocone p c a, codiscreteProductCocone_fresh p c a ha⟩

end SerrePositivity.InfinityCategories.F2.Ind
