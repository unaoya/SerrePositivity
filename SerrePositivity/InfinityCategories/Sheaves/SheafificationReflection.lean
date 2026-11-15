module

public import SerrePositivity.InfinityCategories.Sheaves.SheafCondition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Reflective
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorPresentable
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.BousfieldReflection

/-!
概要：層の充満部分圏と反射の型を固定し、既存のBousfield反射へ接続する。
方針：局所対象と層条件が一致するとき、その同じ部分圏への反射を用いる。
使われ方：HTT 6.2.2.7、Kerodon Tag 06VH の反射による層化。
規約：生成辺の存在と局所性の照合は後続で証明し、この条件付き接続だけで層化存在とはしない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Sheaves
variable {𝒞 : Type u} [SmallCategory 𝒞] {E : SSet.{u+1}} [Quasicategory E]

/-- HTT 1.2.7.3 の前層の関手準圏。 -/
abbrev PresheafCat (𝒞 : Type u) [SmallCategory 𝒞] (E : SSet.{u + 1}) : SSet.{u + 1} :=
  (ihom (presheafShape 𝒞)).obj E

/-- 概要：関手 ∞ 圏の頂点を単体的集合の射として読む。
方針：`functorVertex` の逆（Core/FullSubcomplexInternalHom）。
規約：全単射。
使われ方：`sheafProperty`。
Core の `functorVertexEquiv` を使う。 -/
def vertexToPresheaf (F : (PresheafCat 𝒞 E) _⦋0⦌) : Presheaf 𝒞 E :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm F

/-- 概要：関手 ∞ 圏の頂点が J 層であるという性質。
方針：`IsSheaf` を `vertexToPresheaf` で引き戻す。
規約：Prop。
使われ方：層の充満部分 ∞ 圏、反射。 -/
def sheafProperty (J : GrothendieckTopology 𝒞) : (PresheafCat 𝒞 E) _⦋0⦌ → Prop :=
  fun F => IsSheaf J (vertexToPresheaf F)

/-- 概要：層化のデータ：層への反射。
方針：F2/Presentable の `IsReflectiveSubcategory`（左随伴付きの充満部分圏）。
規約：存在は S4（`sheafification_exists`）。ここでは与えられたものとして使う。
使われ方：RΓ。 -/
abbrev Sheafification (J : GrothendieckTopology 𝒞) (E : SSet.{u + 1}) [Quasicategory E] : Prop :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsReflectiveSubcategory (PresheafCat 𝒞 E) (sheafProperty (E := E) J)

/-- 小さい辺族の局所対象がちょうど層なら、前層圏の Bousfield 反射が層化を与える。 -/
theorem sheafification_of_generatingEdges (J : GrothendieckTopology 𝒞) (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    {I : Type u} (edges : I → (PresheafCat 𝒞 E) _⦋1⦌)
    (hW : ∀ F, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject (X := PresheafCat 𝒞 E) (Set.range edges) F ↔ sheafProperty J F) :
    Sheafification J E := by
  have hP : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (PresheafCat 𝒞 E) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functor_isPresentable (nerve 𝒞ᵒᵖ) hE
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject (X := PresheafCat 𝒞 E) (Set.range edges) =
      sheafProperty (E := E) J :=
    funext fun F => propext (hW F)
  unfold Sheafification
  rw [← h]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfield_isReflectiveSubcategory hP edges


end SerrePositivity.InfinityCategories.Sheaves
