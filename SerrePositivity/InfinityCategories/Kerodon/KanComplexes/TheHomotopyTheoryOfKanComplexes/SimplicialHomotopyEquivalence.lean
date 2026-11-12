module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.MappingSpaceMap
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-!
概要：単体的ホモトピー逆の存在と連結成分への作用。
方針：ホモトピーを各頂点で辺にし、π₀ で逆関数の等式を得る。
規約：実際の区間を用いるホモトピーを使う。
使われ方：Kerodon §4.8.3（Tag 05AW） の写像空間のホモトピー同値性。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：単体的ホモトピーは各頂点の像の間に辺を与える。
方針：頂点での恒等辺と標準区間の辺の積をホモトピーで写す。
規約：辺は時刻零から時刻一へ向く。
使われ方：Kerodon §3.1（Tag 00SZ）、§4.8.3（Tag 05AW） の連結成分への作用。 -/
def simplicialHomotopyVertexEdge {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) (x : X _⦋0⦌) :
    SSet.Edge (f.app (Opposite.op ⦋0⦌) x) (g.app (Opposite.op ⦋0⦌) x) := by
  let e : SSet.Truncated.Edge (X := (truncation 2).obj (X ⊗ Δ[1]))
      (x, stdSimplex.obj₀Equiv.symm 0) (x, stdSimplex.obj₀Equiv.symm 1) :=
    (SSet.Truncated.Edge.id (X := (truncation 2).obj X) x).tensor _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge
  let e' := e.map ((truncation 2).map H.h)
  refine SSet.Edge.mk e'.edge ?_ ?_
  · exact e'.src_eq.trans (ConcreteCategory.congr_hom
      (NatTrans.congr_app H.h₀ (Opposite.op ⦋0⦌)) x)
  · exact e'.tgt_eq.trans (ConcreteCategory.congr_hom
      (NatTrans.congr_app H.h₁ (Opposite.op ⦋0⦌)) x)

/-- 概要：単体的にホモトピックな射は連結成分に同じ写像を誘導する。
方針：零単体の代表へ帰着して、頂点での辺を連結成分の等式にする。
規約：Kan 性や quasicategory 性は不要。
使われ方：Kerodon §4.8.3（Tag 05AW） のホモトピー同値から π₀ の全単射への移行。 -/
lemma mapPiZero_eq_of_homotopy {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) (a : SSet.π₀ X) : SSet.mapπ₀ f a = SSet.mapπ₀ g a := by
  obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective a
  exact SSet.π₀.sound (simplicialHomotopyVertexEdge H x)

/-- 概要：射が単体的ホモトピー逆を持つという条件。
方針：逆射と両合成から恒等射への実際のホモトピーの存在を要求する。
規約：写像空間では A3c の Kan 性の下で用いる。
使われ方：Kerodon Remark 4.8.3.9（Tag 059X） の充満忠実性。 -/
def IsSimplicialHomotopyEquivalence {X Y : SSet.{u}} (f : X ⟶ Y) : Prop :=
  ∃ g : Y ⟶ X, Nonempty (SSet.Homotopy (f ≫ g) (𝟙 X)) ∧
    Nonempty (SSet.Homotopy (g ≫ f) (𝟙 Y))

/-- 概要：恒等射は単体的ホモトピー同値。
方針：恒等射と定値ホモトピーを取る。
規約：任意の単体集合。
使われ方：Kerodon §4.8.3（Tag 05AW） の充満忠実性の恒等射。 -/
lemma isSimplicialHomotopyEquivalence_id (X : SSet.{u}) :
    IsSimplicialHomotopyEquivalence (𝟙 X) := by
  refine ⟨𝟙 X, ?_, ?_⟩
  · rw [Category.id_comp]
    exact ⟨SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm (𝟙 X))⟩
  · rw [Category.id_comp]
    exact ⟨SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm (𝟙 X))⟩

/-- 概要：単体的ホモトピー同値は連結成分の全単射を誘導する。
方針：ホモトピー逆が連結成分上で両側逆になる。
規約：この帰結には Kan 性は不要。
使われ方：Kerodon §4.8.3（Tag 05AW） のホモトピー圏への充満忠実性。 -/
lemma IsSimplicialHomotopyEquivalence.mapPiZero_bijective {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : IsSimplicialHomotopyEquivalence f) : Function.Bijective (SSet.mapπ₀ f) := by
  obtain ⟨g, ⟨H⟩, ⟨K⟩⟩ := hf
  have hleft : Function.LeftInverse (SSet.mapπ₀ g) (SSet.mapπ₀ f) := by
    intro a
    simpa only [SSet.mapπ₀_comp_apply, SSet.mapπ₀_id_apply] using mapPiZero_eq_of_homotopy H a
  have hright : Function.RightInverse (SSet.mapπ₀ g) (SSet.mapπ₀ f) := by
    intro a
    simpa only [SSet.mapπ₀_comp_apply, SSet.mapπ₀_id_apply] using mapPiZero_eq_of_homotopy K a
  exact ⟨hleft.injective, hright.surjective⟩

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
