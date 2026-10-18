module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ColimCoyoneda
public import Mathlib.CategoryTheory.Abelian.CommSq

/-!
概要：Grothendieck アーベル圏の任意の小さい単射族は small object argument を許す。
方針：全ての始域の部分対象を一つの小さい和にまとめ、regular cardinal と単射図式の保存性を得る。
規約：Mathlib の既存の定理から濃度と保存性を証明し、追加フィールドにしない。
使われ方：Stacks 19.12.3・19.12.6、TT §3・§8、Toën §3.2 の非有界 K-injective 分解の構成部品。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w v u
open CategoryTheory Limits MorphismProperty
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {σ : Type w} {A B : σ → C} (i : ∀ s, A s ⟶ B s) [∀ s, Mono (i s)]

/--
概要：小さい単射族が生成する射の性質は単射に含まれる。
方針：指定された族の成分で判定する。
規約：族は実際の射の族。
使われ方：TT §3、Stacks 19.12.6 の超限合成の単射性。
-/
lemma smallMonoFamily_le_monomorphisms : ofHoms i ≤ monomorphisms C := by
  rintro _ _ _ ⟨s⟩
  infer_instance

/--
概要：任意の小さい単射族は small object argument の条件を満たす。
方針：始域の部分対象の和を支配する regular cardinal を選び、単射図式の coyoneda の保存性を使う。
規約：濃度・保存性の存在を別の未証明仮定にしない。
使われ方：Stacks 19.12.3・19.12.6、TT §3・§8、Toën §3.2 の非有界分解。
-/
lemma smallMonoFamily_hasSmallObjectArgument : HasSmallObjectArgument.{w} (ofHoms i) := by
  obtain ⟨κ, hκ', hκ⟩ := HasCardinalLT.exists_regular_cardinal.{w} (Σ s, Subobject (A s))
  have : Fact κ.IsRegular := ⟨hκ'⟩
  have : Nonempty κ.ord.ToType := by simpa using hκ'.ne_zero
  have := WellFoundedLT.toOrderBot κ.ord.ToType
  exact ⟨κ, inferInstance, inferInstance,
    { preservesColimit {X Y Z T} f hf g hg := by
        let hg' : (monomorphisms C).TransfiniteCompositionOfShape κ.ord.ToType g :=
          { toTransfiniteCompositionOfShape := hg.toTransfiniteCompositionOfShape
            map_mem j hj := by
              have h := (hg.attachCells j hj).pushouts_coproducts
              refine (?_ : _ ≤ monomorphisms C) _ h
              simp only [pushouts_le_iff, coproducts_le_iff, ofHoms_homFamily]
              exact smallMonoFamily_le_monomorphisms i }
        have (j j' : κ.ord.ToType) (φ : j ⟶ j') : Mono (hg'.F.map φ) := hg'.mem_map φ
        apply IsGrothendieckAbelian.preservesColimit_coyoneda_obj_of_mono (Y := hg'.F) (κ := κ)
        obtain ⟨s⟩ := hf
        exact hκ.of_injective (fun S : Subobject (A s) => (⟨s, S⟩ : Σ t, Subobject (A t)))
          (by intro S T h; cases h; rfl) }⟩

end SerrePositivity.KST.DerivedGeometry
