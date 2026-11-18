module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalentShapeLimitVertex
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalMap

/-!
概要：同じ指定極限頂点の比較を、元の全錐の同型と明示的な頂点移送に分ける。
方針：等式による移送は等式の帰納法、指定同型は既存の一意性の定義を使う。
規約：HTT §1.2.13、Kerodon §7.1（Tag 02H1）の既存構成の法則。
使われ方：S8 の固定された離散重みの値の同型を変更せずに合成を照合する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 同じ頂点の同型の標的の移送は、同じ頂点等式の射との合成。 -/
lemma vertexIso_transport_target_hom {X : SSet.{u}} {a b c : X _⦋0⦌}
    (h : b = c) (e : VertexIso a b) :
    (h ▸ e).hom = e.hom ≫ eqToHom (congrArg HomotopyCategory.mk h) := by
  cases h
  simp only [eqToHom_refl, Category.comp_id]

/-- 同じ頂点の同型の始域の移送は、元の等式の逆の射との合成。 -/
lemma vertexIso_transport_source_hom {X : SSet.{u}} {a b c : X _⦋0⦌}
    (h : a = b) (e : VertexIso a c) :
    (h ▸ e).hom = eqToHom (congrArg HomotopyCategory.mk h.symm) ≫ e.hom := by
  cases h
  simp only [eqToHom_refl, Category.id_comp]

/-- 図式の固定条件だけを移す比較は、同じ射を持つ cast 錐との標準比較。 -/
lemma limitVertexIsoOfDiagramEq_hom {K X : SSet.{u}} [Quasicategory X]
    {F G : K ⟶ X} (h : F = G) (c : JoinCone F) (d : JoinCone G)
    (hc : IsLimitCone c) (hd : IsLimitCone d) :
    (limitVertexIsoOfDiagramEq h c d hc hd).hom =
      (limitVertexIso (c.cast h) d (hc.cast h) hd).hom := by
  cases h
  rfl

/-- 同値な添字での比較の順射は、同じ制限錐との標準比較と頂点の移送の合成。 -/
lemma limitVertexIsoOfEquivalentRestriction_hom {A B X : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory X]
    (a : A ⟶ B) (ha : IsQCatEquivalence a) (O : B ⟶ X)
    (c : JoinCone (a ≫ O)) (d : JoinCone O) (hc : IsLimitCone c) (hd : IsLimitCone d)
    (hda : IsLimitCone (restrictJoinCone d a)) :
    (limitVertexIsoOfEquivalentRestriction a ha O c d hc hd).hom =
      (limitVertexIso c (restrictJoinCone d a) hc hda).hom ≫
        eqToHom (congrArg HomotopyCategory.mk (restrictJoinCone_vertex d a)) := by
  unfold limitVertexIsoOfEquivalentRestriction
  exact vertexIso_transport_target_hom (restrictJoinCone_vertex d a) _

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
