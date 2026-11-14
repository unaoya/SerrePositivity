module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.StandardLongComparison

/-!
概要：可縮な始域での比較を四因子に分解し、指定した逆因子による終点の相殺を示す。
方針：始域の正準比較の一意性と、終点の同じ射の類の合成を分けて使う。
規約：終点 fiber で辺の一意性を仮定しない。使われ方：指定境界同型による根辺の相殺。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

private lemma arrow_comp_congr {C : Type*} [Category* C] {a b c a' b' c' : C}
    {f : a ⟶ b} {g : b ⟶ c} {f' : a' ⟶ b'} {g' : b' ⟶ c'}
    (hf : Arrow.mk f = Arrow.mk f') (hg : Arrow.mk g = Arrow.mk g') :
    Arrow.mk (f ≫ g) = Arrow.mk (f' ≫ g') := by
  obtain ⟨ha, hb, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp hf
  subst a' b'
  obtain ⟨_, hc, hg⟩ := (Arrow.mk_eq_mk_iff _ _).mp hg
  subst c'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf hg
  subst f' g'
  rfl

private lemma iso_inv_hom_arrow {C : Type*} [Category* C] {a b a' b' : C}
    (I : a ≅ b) (J : a' ≅ b') (h : Arrow.mk I.hom = Arrow.mk J.hom) :
    Arrow.mk I.inv = Arrow.mk J.inv := by
  obtain ⟨ha, hb, h⟩ := (Arrow.mk_eq_mk_iff _ _).mp h
  subst a' b'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h
  have he : I = J := Iso.ext h
  subst J
  rfl

/-- 同じ射として照合した二つの頂点同型は、同じ評価後も同じ射となる。 -/
lemma vertexIso_map_hom_arrow {X Y : SSet.{u}} {a b c d : X _⦋0⦌}
    (F : X ⟶ Y) {I : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso a b} {J : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso c d}
    (h : Arrow.mk I.hom = Arrow.mk J.hom) :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map I F).hom = Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map J F).hom :=
  congrArg (hoFunctor.map F).toFunctor.mapArrow.obj h

/-- 三因子の積の逆は、同じ射で写した三因子の積の逆へ写る。 -/
lemma vertexIso_map_inverse_threeFactors {X Y : SSet.{u}} {a b c d : X _⦋0⦌}
    (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso a b) (M : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso b c) (R : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso d c) (F : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (L ≪≫ M ≪≫ R.symm).symm F =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map L F ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map M F ≪≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map R F).symm).symm := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexIso_map_symm, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexIso_map_trans, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexIso_map_trans, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexIso_map_symm]

/-- 同じ可縮な始域の比較は、指定した四因子の像の積である。 -/
lemma contractibleVertexIso_endpoint_fourFactors {X Y : SSet.{u}} (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan X)
    (F : X ⟶ Y) (w x y z w' : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (hX.vertexIso w w') F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (hX.vertexIso w x) F ≪≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (hX.vertexIso x y) F ≪≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (hX.vertexIso z y) F).symm ≪≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (hX.vertexIso z w') F := by
  have he : hX.vertexIso w w' = hX.vertexIso w x ≪≫ hX.vertexIso x y ≪≫
      (hX.vertexIso z y).symm ≪≫ hX.vertexIso z w' := by
    have := hX.kanComplex
    apply Iso.ext
    exact (hX.isTerminalVertex w').isTerminalHo.hom_ext _ _
  rw [he, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexIso_map_trans, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexIso_map_trans, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexIso_map_trans, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexIso_map_symm]

/-- 四因子の終点が指定した三因子とその積の逆なら、全比較の終点は恒等射である。 -/
lemma contractibleVertexIso_endpoint_cancel {X Y : SSet.{u}} (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan X)
    (F : X ⟶ Y) (w x y z w' : X _⦋0⦌)
    {a b c d : hoFunctor.obj Y} (L : a ≅ b) (M : b ≅ c) (R : d ≅ c)
    (hL : Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (hX.vertexIso w x) F).hom = Arrow.mk L.hom)
    (hM : Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (hX.vertexIso x y) F).hom = Arrow.mk M.hom)
    (hR : Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (hX.vertexIso z y) F).hom = Arrow.mk R.hom)
    (hK : Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (hX.vertexIso z w') F).hom =
      Arrow.mk (L ≪≫ M ≪≫ R.symm).inv) :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (hX.vertexIso w w') F).hom = Arrow.mk (𝟙 a) := by
  have hF := contractibleVertexIso_endpoint_fourFactors hX F w x y z w'
  have hp := arrow_comp_congr hL
    (arrow_comp_congr hM (arrow_comp_congr (iso_inv_hom_arrow _ _ hR) hK))
  refine (congrArg (fun I ↦ Arrow.mk I.hom) hF).trans ?_
  refine hp.trans ?_
  simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id, Iso.hom_inv_id_assoc]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
