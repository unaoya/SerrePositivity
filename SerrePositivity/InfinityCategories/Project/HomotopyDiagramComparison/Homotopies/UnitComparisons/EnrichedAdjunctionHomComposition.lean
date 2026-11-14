module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderPostcomposition

/-!
概要：豊穣随伴の Hom 同型に関する右変数の合成と、元の通常随伴との零単体の互換データ。
方針：全次数の合成互換を明示し、通常の随伴だけからは仮定しない。
規約：モデル圏の条件は不要。使われ方：HTT 5.2.4.6 の左混合辺の写像空間比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory HomotopicalAlgebra MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {C : Type v} {D : Type w} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D] (R : EnrichedFunctor SSet.{u} D C)

/-- 元の通常随伴と両立し、右変数の豊穣合成を保つ Hom 同型のデータ。 -/
structure EnrichedAdjunctionHomComposition {L : C ⥤ D}
    (adj : L ⊣ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R) where
  /-- 元の左右の豊穣 Hom の同型。 -/
  homIso : ∀ X Y, (L.obj X ⟶[SSet.{u}] Y) ≅ (X ⟶[SSet.{u}] R.obj Y)
  /-- 右変数の全写像空間に対する合成互換。 -/
  hom_comp : ∀ X Y Z, eComp SSet (L.obj X) Y Z ≫ (homIso X Z).hom =
    ((homIso X Y).hom ⊗ₘ R.map Y Z) ≫ eComp SSet X (R.obj Y) (R.obj Z)
  /-- 元の通常随伴の射と豊穣単位からの射の一致。 -/
  hom_zero : ∀ X Y (f : L.obj X ⟶ Y),
    eHomEquiv SSet f ≫ (homIso X Y).hom = eHomEquiv SSet (adj.homEquiv X Y f)


variable {L : C ⥤ D} (adj : L ⊣ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R)
variable (e : EnrichedAdjunctionHomComposition R adj)

/-- 豊穣合成互換により、元の左射の前合成を随伴像の混合合成へ移す。 -/
lemma enrichedAdjunctionHom_precompose (X : C) (Y Z : D) (f : L.obj X ⟶ Y) :
    eHomWhiskerRight SSet f Z ≫ (e.homIso X Z).hom =
      (λ_ (Y ⟶[SSet] Z)).inv ≫ eHomEquiv SSet (adj.homEquiv X Y f) ▷ _ ≫
        (𝟙 _ ⊗ₘ R.map Y Z) ≫ eComp SSet X (R.obj Y) (R.obj Z) := by
  unfold eHomWhiskerRight
  rw [Category.assoc, Category.assoc, e.hom_comp]
  simp only [tensorHom_def, Category.assoc, id_whiskerRight, Category.id_comp]
  rw [← comp_whiskerRight_assoc, e.hom_zero]
  rfl

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
