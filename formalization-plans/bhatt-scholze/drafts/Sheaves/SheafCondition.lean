-- 将来の置き場所：SerrePositivity.InfinityCategories.Sheaves.SheafCondition（層 Sheaves、StablePresentable < Sheaves < ModelBridge）
-- 設計書：formalization-plans/bhatt-scholze/infinity-sheaves-design.md §1・§3、単位 S1。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalMap
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cone
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseLimits
public import Mathlib.CategoryTheory.Sites.Coherent.ExtensiveSheaves
public import Mathlib.CategoryTheory.Sites.Grothendieck
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# ∞ 圏に値をとる前層の層条件（HTT 6.2.2.6）

## 概要
小さい圏 𝒞 の Grothendieck 位相 J と ∞ 圏 E について、E 値前層 F : N(𝒞)^op → E が J 層であることを、
被覆篩 S ⊆ h_U ごとに「F(U) を頂点とする S 上の制限図式の錐が極限錐である」こととして定義する。
位相データ（篩・被覆）は Mathlib の `GrothendieckTopology`・`Sieve` をそのまま使う。

## 方針
篩 S の射 (V → U) のなす圏（Over U の充満部分圏）上の図式 (V → U) ↦ F(V) を、1 圏の錐（頂点 U、脚 f）の nerve
（`F1B.nerveCone`）を F で後合成して作る。極限性は `Core.IsLimitCone`。E が安定・presentable であることはここでは仮定しない。

## 規約
層は被覆篩に沿う降下（Čech 層）であり、hypercover に沿う降下（hypersheaf）ではない。両者は有界（特に離散）な前層では一致し、
非有界な前層では一致しないことがある（設計書 §2.1、勉強ノート第 4 章 D17）。小さい形状は `SSet.{u}`、E は `SSet.{u+1}` で、
形状は `SSet.uliftFunctor` で持ち上げる（F2/Presentable の約束）。

## 使われ方
S2（Γ・RΓ）、S4（層化：層 ⇔ 局所対象）、Cor 3.12(d)（prismatic site の O_Δ が層）、A5（完全 prismatic site）、A6（arc 位相）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Sheaves

variable {𝒞 : Type u} [SmallCategory 𝒞] {E : SSet.{u + 1}} [Quasicategory E]

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
規約：𝒞 が小さいのでこの圏も小さい。
使われ方：S 上の制限図式の添字。HTT 6.2.2.6 の「S の元の圏」。 -/
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
        rw [Category.id_comp, ← Quiver.Hom.op_comp, Over.w f.unop.hom] }

/-- 概要：前層 F の篩 S 上への制限図式。
方針：篩の圏の nerve を持ち上げ、`nerveMap (sieveDiagram S)` を F に前合成する。
規約：添字は `presheafShape (sieveCategory S)`。
使われ方：層条件の図式。 -/
def restriction (F : Presheaf 𝒞 E) {U : 𝒞} (S : Sieve U) :
    presheafShape (sieveCategory S) ⟶ E :=
  (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (sieveDiagram S)) ≫ F

/-- 概要：join の錐を `uliftFunctor` で一つ上の宇宙へ持ち上げる。
方針：`uliftFunctor` が join と Δ[0] を保つ同型で、錐の射と固定条件を移す。
規約：頂点は元の頂点の持ち上げ。
使われ方：1 圏の錐の nerve（SSet.{u}）を E（SSet.{u+1}）上の錐にするため。
実装は Core/UniverseLimits の既存の錐の持ち上げ。 -/
abbrev JoinCone.ulift {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCone p) :
    JoinCone ((SSet.uliftFunctor.{u + 1, u}).map p) :=
  SerrePositivity.InfinityCategories.JoinCone.ulift.{u,u+1} c

/-- 概要：F(U) を頂点とする、F の S 上の制限図式の錐。
方針：1 圏の錐 `sieveCone S` を `F1B.nerveCone` で nerve の join 錐にし、持ち上げてから F で後合成する。
規約：脚は F(f)。頂点は F(op U)。
使われ方：層条件はこの錐の極限性。 -/
def restrictionCone (F : Presheaf 𝒞 E) {U : 𝒞} (S : Sieve U) : JoinCone (restriction F S) :=
  ((F1B.nerveCone (sieveCone S)).ulift).postcomp F

/-- 概要：E 値前層 F が位相 J の層である（HTT 6.2.2.6 の E 値版）。
方針：すべての被覆篩 S ∈ J U について `restrictionCone F S` が極限錐。
規約：Čech 層。hypersheaf ではない（モジュールの規約を参照）。E に極限の存在は仮定しない。
使われ方：層化の像、Γ の定義域、Cor 3.12(d)。 -/
def IsSheaf (J : GrothendieckTopology 𝒞) (F : Presheaf 𝒞 E) : Prop :=
  ∀ (U : 𝒞) (S : Sieve U), S ∈ J U → IsLimitCone (restrictionCone F S)

/-- 概要：粗い位相の層は細かい位相でも…ではなく、細かい位相の層は粗い位相の層である。
方針：被覆篩の包含。
規約：J ≤ J′ は J の被覆篩が J′ の被覆篩であること（Mathlib の順序）。
使われ方：生成位相との比較。 -/
lemma IsSheaf.of_le {J J' : GrothendieckTopology 𝒞} (h : J ≤ J') {F : Presheaf 𝒞 E}
    (hF : IsSheaf J' F) : IsSheaf J F :=
  fun U S hS => hF U S (h U hS)

/-- 概要：最小の位相（被覆篩は最大篩だけ）ではすべての前層が層。
方針：最大篩の圏は終対象 (U, 𝟙) を持ち、錐は自明に極限錐。
規約：`⊥` は Mathlib の `GrothendieckTopology` の完備束の底。
使われ方：位相によらない議論の端。 -/
lemma isSheaf_bot (F : Presheaf 𝒞 E) : IsSheaf ⊥ F := by
  sorry -- 最大篩の圏の終対象と `WeaklyContractibleConstantLimit` 型の補題

/-- 概要：生成系での降下から全被覆篩での降下を出す（Mathlib `Presieve.isSheaf_coverage` の ∞ 版）。
方針：`Coverage` の引き戻し安定性と、篩の生成に沿う極限の合成。
規約：K は coverage（引き戻しで refine できる被覆族）、J = K.toGrothendieck。
使われ方：Cor 3.12(d)：忠実平坦な単射の篩での降下で十分。
要確認：∞ 版の証明は HTT 6.2.2 の議論を要する。S1 の中で最も重い。 -/
theorem isSheaf_toGrothendieck_iff (K : Coverage 𝒞) (F : Presheaf 𝒞 E) :
    IsSheaf K.toGrothendieck F ↔
      ∀ (U : 𝒞) (R : Presieve U), R ∈ K.coverings U →
        IsLimitCone (restrictionCone F (Sieve.generate R)) := by
  sorry -- HTT 6.2.2 系の一般論（生成系での降下で十分）

/-- 有限積の指定された錐を F で送ったものが極限錐。空族を含む。 -/
def PreservesFiniteProductsOnSite (F : Presheaf 𝒞 E) : Prop :=
  ∀ (ι : Type u) [Finite ι] (B : ι → 𝒞ᵒᵖ) (c : Fan B), Nonempty (IsLimit c) →
    IsLimitCone (mapJoinCone F (SerrePositivity.InfinityCategories.JoinCone.ulift.{u,u+1} (F1B.nerveCone c)))

/-- S1-E。有限余積が普遍かつ非交叉な site での extensive 位相の層判定。 -/
theorem isSheaf_extensive_iff_preservesFiniteProducts {E : SSet.{u+1}} [Quasicategory E]
    [FinitaryExtensive 𝒞] (F : Presheaf 𝒞 E) :
    IsSheaf (extensiveTopology 𝒞) F ↔ PreservesFiniteProductsOnSite F := by
  sorry -- 異なる余積の脚の交叉は始対象。空被覆の条件と各余積被覆の降下で積錐を判定

/-- J と J′ の被覆を合わせて生成した位相の層条件。 -/
theorem isSheaf_sup_iff {E : SSet.{u+1}} [Quasicategory E] (J J' : GrothendieckTopology 𝒞) (F : Presheaf 𝒞 E) :
    IsSheaf (J ⊔ J') F ↔ IsSheaf J F ∧ IsSheaf J' F := by
  sorry -- 一方向は of_le。逆向きは二つの位相の被覆を合わせた生成系での降下

end SerrePositivity.InfinityCategories.Sheaves
