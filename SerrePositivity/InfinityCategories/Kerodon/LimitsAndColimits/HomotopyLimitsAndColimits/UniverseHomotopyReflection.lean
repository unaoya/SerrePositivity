module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedConeSectionEquivalence

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseSSetMaps
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.UniverseHomotopy

/-!
概要：単体集合の宇宙の持ち上げは実際の単体的ホモトピー同値性を検出する。
方針：区間の単体を同定してホモトピーを戻し、充満性でホモトピー逆を戻す。
規約：元の単体集合にも持ち上げた単体集合にも Kan 性は要求しない。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、元の q_x の同値性の逆向きの判定。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
noncomputable section

/-- 概要：持ち上げた二射の実際の単体的ホモトピーを元の宇宙へ戻す。
方針：区間の各単体を包み直し、値の ULift を外して評価する。
規約：両端点をそのまま保ち、Kan 性は不要。
使われ方：持ち上げたホモトピー逆を元の宇宙へ戻す。 -/
def uliftHomotopyDown {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy ((SSet.uliftFunctor.{v, u}).map f)
      ((SSet.uliftFunctor.{v, u}).map g)) : SSet.Homotopy f g where
  h :=
    { app d := ↾fun z ↦ (H.h.app d (ULift.up z.1, ULift.up z.2.down)).down
      naturality {a b} α := by
        apply ConcreteCategory.hom_ext
        intro z
        exact congrArg (fun q :
          ((SSet.uliftFunctor.{v, u}).obj X ⊗ (Δ[1] : SSet.{max u v})).obj a ⟶
            ((SSet.uliftFunctor.{v, u}).obj Y).obj b ↦
              (q (ULift.up z.1, ULift.up z.2.down)).down) (H.h.naturality α) }
  h₀ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    exact congrArg (fun k : (SSet.uliftFunctor.{v, u}).obj X ⟶
      (SSet.uliftFunctor.{v, u}).obj Y ↦ (k.app d (ULift.up z)).down) H.h₀
  h₁ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    exact congrArg (fun k : (SSet.uliftFunctor.{v, u}).obj X ⟶
      (SSet.uliftFunctor.{v, u}).obj Y ↦ (k.app d (ULift.up z)).down) H.h₁
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- 概要：持ち上げた射が単体的ホモトピー逆を持てば元の射も持つ。
方針：逆射を充満性で戻し、両合成のホモトピーを元の宇宙へ戻す。
規約：Kan 性や宇宙の大小関係を仮定しない。
使われ方：反転した元の比較射の同値性を ULift 後の判定から戻す。 -/
lemma homotopyEquivalence_of_ulift {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence ((SSet.uliftFunctor.{v, u}).map f)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence f := by
  obtain ⟨g, ⟨H⟩, ⟨G⟩⟩ := hf
  let g₀ := (SSet.uliftFunctor.{v, u}).preimage g
  have hg : (SSet.uliftFunctor.{v, u}).map g₀ = g := Functor.map_preimage _ _
  have H' : SSet.Homotopy ((SSet.uliftFunctor.{v, u}).map (f ≫ g₀))
      ((SSet.uliftFunctor.{v, u}).map (𝟙 X)) := by
    rw [(SSet.uliftFunctor.{v, u}).map_comp f g₀,
      (SSet.uliftFunctor.{v, u}).map_id X, hg]
    exact H
  have G' : SSet.Homotopy ((SSet.uliftFunctor.{v, u}).map (g₀ ≫ f))
      ((SSet.uliftFunctor.{v, u}).map (𝟙 Y)) := by
    rw [(SSet.uliftFunctor.{v, u}).map_comp g₀ f,
      (SSet.uliftFunctor.{v, u}).map_id Y, hg]
    exact G
  exact ⟨g₀, ⟨uliftHomotopyDown H'⟩, ⟨uliftHomotopyDown G'⟩⟩

/-- 概要：単体的ホモトピー同値性は宇宙の持ち上げの前後で同値。
方針：既存の保存とホモトピー逆の降下を組み合わせる。
規約：全ての単体集合の射に適用できる。
使われ方：元の q_x と持ち上げた反転比較の同値性の照合。 -/
lemma ulift_homotopyEquivalence_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence ((SSet.uliftFunctor.{v, u}).map f) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence f :=
  ⟨homotopyEquivalence_of_ulift f, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ulift_homotopyEquivalence⟩

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
