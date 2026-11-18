module

public meta import SerrePositivity.Util.Citation

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cone
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseLimits
public import Mathlib.CategoryTheory.Sites.Grothendieck
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
概要：小さい通常siteの篩上の指定制限錐と、準圏値のČech層条件。
方針：篩の射の充満部分圏の錐をnerve・宇宙持ち上げ・後合成で運ぶ。
  文献対応：HTT 6.2.2.6、Kerodon §7.1（Tag 02H1）の指定錐による層条件。
規約：層はČech層。被覆生成・層化は後続の定理で示す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
namespace SerrePositivity.InfinityCategories.Sheaves
variable {𝒞 : Type u} [SmallCategory 𝒞] {E : SSet.{u+1}} [Quasicategory E]

/-- 概要：小さい圏 𝒞 の nerve の opposite を一つ上の宇宙へ持ち上げた、前層の添字。
方針：E が SSet.{u+1} なので、形状を `uliftFunctor` で合わせる。
規約：𝒞ᵒᵖ の nerve を取る（E 値の反変関手）。
使われ方：前層・層・大域切断の添字。 -/
abbrev presheafShape (𝒞 : Type u) [SmallCategory 𝒞] : SSet.{u + 1} :=
  (SSet.uliftFunctor.{u + 1, u}).obj (nerve 𝒞ᵒᵖ)

/-- 概要：E 値前層。HTT 1.2.7.3 の Fun(N(𝒞)^op, E) の頂点。
方針：単体的集合の射として扱い、関手 ∞ 圏の頂点との対応は S2 で `functorVertex` により付ける。
規約：E の quasicategory 性だけを仮定する。
使われ方：層条件、層化、Γ。 -/
abbrev Presheaf (𝒞 : Type u) [SmallCategory 𝒞] (E : SSet.{u + 1}) := presheafShape 𝒞 ⟶ E

/-- 概要：篩 S の射 (V → U) のなす圏（Over U の、S に属する射の充満部分圏）。
方針：Mathlib の `Over` と `ObjectProperty.FullSubcategory`。
  文献対応：S 上の制限図式の添字。HTT 6.2.2.6 の「S の元の圏」。
規約：𝒞 が小さいのでこの圏も小さい。
-/
def sieveCategory {U : 𝒞} (S : Sieve U) : Type u :=
  ObjectProperty.FullSubcategory (fun f : Over U => S.arrows f.hom)

instance {U : 𝒞} (S : Sieve U) : SmallCategory (sieveCategory S) := by
  unfold sieveCategory; infer_instance

/-- 概要：篩の圏から 𝒞ᵒᵖ への図式 (V → U) ↦ V（opposite）。
方針：充満部分圏の包含と `Over.forget` の合成の opposite。
規約：添字は (sieveCategory S)ᵒᵖ。
使われ方：F を制限する形状の射。 -/
def sieveDiagram {U : 𝒞} (S : Sieve U) : (sieveCategory S)ᵒᵖ ⥤ 𝒞ᵒᵖ :=
  (ObjectProperty.ι _ ⋙ Over.forget U).op

/-- 概要：頂点 U、脚 f の 1 圏の錐（𝒞ᵒᵖ の中で）。
方針：各 (V →f U) について f.op : op U ⟶ op V。自然性は Over の射の可換性。
規約：これは 𝒞ᵒᵖ の錐で、F で送る前のもの。
使われ方：`restrictionCone` の材料。 -/
def sieveCone {U : 𝒞} (S : Sieve U) : Cone (sieveDiagram S) where
  pt := Opposite.op U
  π :=
    { app := fun f => (f.unop.obj.hom).op
      naturality := by
        -- Over U の射 g : f → f' は g.left ≫ f'.hom = f.hom を満たす。
        intro x y f
        change 𝟙 (Opposite.op U) ≫ y.unop.obj.hom.op =
          x.unop.obj.hom.op ≫ f.unop.hom.left.op
        rw [Category.id_comp, ← _root_.CategoryTheory.op_comp, Over.w f.unop.hom] }

/-- 概要：前層 F の篩 S 上への制限図式。
方針：篩の圏の nerve を持ち上げ、`nerveMap (sieveDiagram S)` を F に前合成する。
規約：添字は `presheafShape (sieveCategory S)`。
使われ方：層条件の図式。 -/
def restriction (F : Presheaf 𝒞 E) {U : 𝒞} (S : Sieve U) :
    presheafShape (sieveCategory S) ⟶ E :=
  (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (sieveDiagram S)) ≫ F

/-- 概要：F(U) を頂点とする、F の S 上の制限図式の錐。
方針：1 圏の錐 `sieveCone S` を `SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone` で nerve の join 錐にし、持ち上げてから F で後合成する。
規約：脚は F(f)。頂点は F(op U)。
使われ方：層条件はこの錐の極限性。 -/
def restrictionCone (F : Presheaf 𝒞 E) {U : 𝒞} (S : Sieve U) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (restriction F S) :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone (sieveCone S)).ulift).postcomp F

/-- 概要：E 値前層 F が位相 J の層である（HTT 6.2.2.6 の E 値版）。
方針：すべての被覆篩 S ∈ J U について `restrictionCone F S` が極限錐。
規約：Čech 層。hypersheaf ではない（モジュールの規約を参照）。E に極限の存在は仮定しない。
使われ方：層化の像、Γ の定義域、Cor 3.12(d)。 -/
@[cite HTT "6.2.2.6" (partial := special)
  "小さい通常の site の nerve に限る Čech 層条件。空間値の定義を一般の準圏値で定式化する。"]
def IsSheaf (J : GrothendieckTopology 𝒞) (F : Presheaf 𝒞 E) : Prop :=
  ∀ (U : 𝒞) (S : Sieve U), S ∈ J U → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (restrictionCone F S)

/-- 概要：粗い位相の層は細かい位相でも…ではなく、細かい位相の層は粗い位相の層である。
方針：被覆篩の包含。
規約：J ≤ J′ は J の被覆篩が J′ の被覆篩であること（Mathlib の順序）。
使われ方：生成位相との比較。 -/
lemma IsSheaf.of_le {J J' : GrothendieckTopology 𝒞} (h : J ≤ J') {F : Presheaf 𝒞 E}
    (hF : IsSheaf J' F) : IsSheaf J F :=
  fun U S hS => hF U S (h U hS)


end SerrePositivity.InfinityCategories.Sheaves
