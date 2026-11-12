module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PullbackEdgeRepresentatives

/-!
概要：基底で整合する成分同型から、元の引き戻しの頂点同型を構成する。
方針：同型の辺代表の像を合わせ、公開された辺代表修正と可逆性の反映を使う。
規約：引き戻しの頂点が持つ基底の等式を明示的な同型として保持する。
使われ方：実現される基底同型で添字付けた小さい compact 代表族の被覆。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

private lemma edgeHom_transport {C : SSet.{u}} {x y x' y' : C _⦋0⦌}
    (hx : x = x') (hy : y = y')
    (f : SSet.Truncated.Edge (X := (truncation 2).obj C) x y)
    (g : SSet.Truncated.Edge (X := (truncation 2).obj C) x' y') (h : f.edge = g.edge) :
    SSet.Truncated.HomotopyCategory.homMk f =
      eqToHom (congrArg HomotopyCategory.mk hx) ≫
        SSet.Truncated.HomotopyCategory.homMk g ≫
        eqToHom (congrArg HomotopyCategory.mk hy.symm) := by
  subst x'
  subst y'
  have hfg : f = g := SSet.Truncated.Edge.ext h
  subst g
  simp

/-- 概要：引き戻し頂点の第二成分の像から第一成分の像への指定同型。
方針：元の引き戻しの厳密な等式をホモトピー圏の同型へ移す。
規約：向きは第二から第一。
使われ方：成分同型の整合を一つの基底同型で記録する。 -/
def pullbackVertexBaseIso {E D B : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B)
    (x : (pullback p q) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (q.app _ ((pullback.snd p q).app _ x))
      (p.app _ ((pullback.fst p q).app _ x)) :=
  eqToIso (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex_compat p q x).symm)

/-- 概要：基底同型と整合する二成分の頂点同型は元の引き戻し内の頂点同型を与える。
方針：辺代表の類の整合を端点の移送で示し、引き戻し内の可逆な辺へ貼り合わせる。
規約：成分同型の存在だけではなく、基底での整合を要求する。
使われ方：小さい候補族が同じ基底同型の全実現を代表することの証明。 -/
lemma exists_pullbackVertexIso_of_compatible_components {E D B : SSet.{u}}
    [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) [InnerFibration p]
    {x y : (pullback p q) _⦋0⦌}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((pullback.fst p q).app _ x) ((pullback.fst p q).app _ y))
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((pullback.snd p q).app _ x) ((pullback.snd p q).app _ y))
    (h : pullbackVertexBaseIso p q x ≪≫ e.map p =
      d.map q ≪≫ pullbackVertexBaseIso p q y) : Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y) := by
  obtain ⟨f, hf⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ e.hom
  obtain ⟨g, hg⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ d.hom
  have ht := edgeHom_transport (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex_compat p q x)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex_compat p q y) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackSecondEdgeInBase p q g)
    (g.map ((truncation 2).map q)) rfl
  have hc : SSet.Truncated.HomotopyCategory.homMk (f.map ((truncation 2).map p)) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackSecondEdgeInBase p q g) := by
    rw [ht]
    change (hoFunctor.map p).toFunctor.map (SSet.Truncated.HomotopyCategory.homMk f) =
      _ ≫ (hoFunctor.map q).toFunctor.map (SSet.Truncated.HomotopyCategory.homMk g) ≫ _
    rw [hf, hg]
    have hh := congrArg Iso.hom h
    change (pullbackVertexBaseIso p q x).hom ≫ (e.map p).hom =
      (d.map q).hom ≫ (pullbackVertexBaseIso p q y).hom at hh
    have hx := congrArg (fun k ↦ (pullbackVertexBaseIso p q x).inv ≫ k) hh
    change (e.map p).hom = (pullbackVertexBaseIso p q x).inv ≫
      (d.map q).hom ≫ (pullbackVertexBaseIso p q y).hom
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hx
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_pullbackVertexIso_of_component_edge_classes p q f g hc
  · change IsIso (SSet.Truncated.HomotopyCategory.homMk f)
    rw [hf]
    infer_instance
  · change IsIso (SSet.Truncated.HomotopyCategory.homMk g)
    rw [hg]
    infer_instance

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
