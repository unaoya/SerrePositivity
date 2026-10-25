module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarAugmentation
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.AppendSimplex

/-!
概要：終頂点を持つ poset 上のホモロジー bar の末尾付加。
方針：各単体へ最大頂点を付け、始点係数を同じまま運ぶ。
規約：元の G ではなく、ホモロジーを取った後の通常の図式に適用する。
使われ方：filtered poset の下方部分圏での bar の局所縮約。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits Opposite SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] {J : Type u} [PartialOrder J] [OrderTop J]
  (F : J ⥤ ModuleCat.{u} R)

def dgHomologyBarTopCocone : Cocone F where
  pt := F.obj ⊤
  ι :=
    { app j := F.map (homOfLE (le_top : j ≤ ⊤))
      naturality j k f := by
        dsimp
        rw [Category.comp_id, ← F.map_comp]
        congr 1 }

def dgHomologyBarAppend (n : ℕ) :
    (dgHomologyBarSimplicial R F) _⦋n⦌ ⟶ (dgHomologyBarSimplicial R F) _⦋n + 1⦌ :=
  Sigma.desc (fun s =>
    F.map (eqToHom (dgStrictAppendSimplex_obj_castSucc s ⊤ le_top 0).symm) ≫
      Sigma.ι (dgHomologyBarFamily R F (op ⦋n + 1⦌)) (dgStrictAppendSimplex s ⊤ le_top))

@[reassoc (attr := simp)]
lemma dgHomologyBarAppend_ι (n : ℕ) (s : (nerve J) _⦋n⦌) :
    Sigma.ι (dgHomologyBarFamily R F (op ⦋n⦌)) s ≫ dgHomologyBarAppend R F n =
      F.map (eqToHom (dgStrictAppendSimplex_obj_castSucc s ⊤ le_top 0).symm) ≫
        Sigma.ι (dgHomologyBarFamily R F (op ⦋n + 1⦌))
          (dgStrictAppendSimplex s ⊤ le_top) := by
  simp only [dgHomologyBarAppend, Sigma.ι_comp_desc]

lemma dgHomologyBarTransport_ι {Δ : SimplexCategoryᵒᵖ} {s t : (nerve J).obj Δ}
    (h : s = t) (f : s.obj 0 ⟶ t.obj 0) :
    F.map f ≫ Sigma.ι (dgHomologyBarFamily R F Δ) t =
      Sigma.ι (dgHomologyBarFamily R F Δ) s := by
  subst t
  have hf : f = 𝟙 (s.obj 0) := Subsingleton.elim _ _
  rw [hf, F.map_id, Category.id_comp]

lemma dgHomologyBarCoefficient_transport {Δ : SimplexCategoryᵒᵖ}
    {s t : (nerve J).obj Δ} (h : s = t) {a : J} (f : a ⟶ s.obj 0) (g : a ⟶ t.obj 0) :
    F.map f ≫ Sigma.ι (dgHomologyBarFamily R F Δ) s =
      F.map g ≫ Sigma.ι (dgHomologyBarFamily R F Δ) t := by
  subst t
  rw [Subsingleton.elim f g]

lemma dgHomologyBarAppend_face_last (n : ℕ) :
    dgHomologyBarAppend R F n ≫ (dgHomologyBarSimplicial R F).δ (Fin.last (n + 1)) = 𝟙 _ := by
  apply Sigma.hom_ext
  intro s
  erw [← Category.assoc, dgHomologyBarAppend_ι, Category.assoc, dgHomologyBarMap_ι,
    ← Category.assoc, ← F.map_comp]
  have hs := dgStrictAppendSimplex_face_last s ⊤ (le_top : s.obj (Fin.last n) ≤ ⊤)
  erw [Category.comp_id]
  exact dgHomologyBarTransport_ι R F hs.symm _

lemma dgHomologyBarAppend_face (n : ℕ) (i : Fin (n + 2)) :
    dgHomologyBarAppend R F (n + 1) ≫ (dgHomologyBarSimplicial R F).δ i.castSucc =
      (dgHomologyBarSimplicial R F).δ i ≫ dgHomologyBarAppend R F n := by
  apply Sigma.hom_ext
  intro s
  simp only [SimplicialObject.δ, dgHomologyBarSimplicial, Category.assoc,
    dgHomologyBarAppend_ι_assoc, dgHomologyBarMap_ι_assoc,
    dgHomologyBarAppend_ι, dgHomologyBarMap_ι]
  rw [← Category.assoc, ← F.map_comp, ← Category.assoc, ← F.map_comp]
  exact dgHomologyBarCoefficient_transport R F
    (dgStrictAppendSimplex_face_castSucc s ⊤ le_top i) _ _

end SerrePositivity.InfinityCategories
