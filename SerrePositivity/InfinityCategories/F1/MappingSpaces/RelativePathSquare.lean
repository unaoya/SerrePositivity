module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullSubcomplexPathLift
public import SerrePositivity.InfinityCategories.Core.RelativeEquivalencePathAt

/-!
概要：可換四角形に沿う相対可逆 path の比較。
方針：path の像と指定端点を、それぞれ可換四角形の射で写す。
規約：全ての端点の等式は厳密に保つ。
使われ方：反転関手の制限の可逆 path 持ち上げを周囲の関手空間へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 可換四角形は、path と指定端点の組の間の実際の射を誘導する。 -/
def relativePathSquareTargetMap {A B X Y : SSet.{u}} (p : A ⟶ B) (q : X ⟶ Y)
    (a : A ⟶ X) (b : B ⟶ Y) (h : p ≫ b = a ≫ q) (j : Fin 2) :
    relativeEquivalencePathTargetAt p j ⟶ relativeEquivalencePathTargetAt q j :=
  pullback.lift
    (pullback.fst (equivalencePathEndpoint B j) p ≫ equivalencePathMap b)
    (pullback.snd (equivalencePathEndpoint B j) p ≫ a) (by
      rw [Category.assoc, equivalencePathMap_endpoint, ← Category.assoc,
        pullback.condition, Category.assoc, h, ← Category.assoc])

/-- 相対 path の標的の比較は、path の成分と可換。 -/
lemma relativePathSquareTargetMap_fst {A B X Y : SSet.{u}} (p : A ⟶ B) (q : X ⟶ Y)
    (a : A ⟶ X) (b : B ⟶ Y) (h : p ≫ b = a ≫ q) (j : Fin 2) :
    relativePathSquareTargetMap p q a b h j ≫
        pullback.fst (equivalencePathEndpoint Y j) q =
      pullback.fst (equivalencePathEndpoint B j) p ≫ equivalencePathMap b :=
  pullback.lift_fst _ _ _

/-- 相対 path の標的の比較は、指定端点の成分と可換。 -/
lemma relativePathSquareTargetMap_snd {A B X Y : SSet.{u}} (p : A ⟶ B) (q : X ⟶ Y)
    (a : A ⟶ X) (b : B ⟶ Y) (h : p ≫ b = a ≫ q) (j : Fin 2) :
    relativePathSquareTargetMap p q a b h j ≫
        pullback.snd (equivalencePathEndpoint Y j) q =
      pullback.snd (equivalencePathEndpoint B j) p ≫ a :=
  pullback.lift_snd _ _ _

/-- 相対可逆 path の写像は、可換四角形による比較と厳密に可換。 -/
lemma relativePathSquare_comm {A B X Y : SSet.{u}} (p : A ⟶ B) (q : X ⟶ Y)
    (a : A ⟶ X) (b : B ⟶ Y) (h : p ≫ b = a ≫ q) (j : Fin 2) :
    relativeEquivalencePathMapAt p j ≫ relativePathSquareTargetMap p q a b h j =
      equivalencePathMap a ≫ relativeEquivalencePathMapAt q j := by
  apply pullback.hom_ext
  · rw [Category.assoc, relativePathSquareTargetMap_fst, ← Category.assoc,
      relativeEquivalencePathMapAt_fst, ← equivalencePathMap_comp,
      Category.assoc, relativeEquivalencePathMapAt_fst, ← equivalencePathMap_comp, h]
  · rw [Category.assoc, relativePathSquareTargetMap_snd, ← Category.assoc,
      relativeEquivalencePathMapAt_snd, Category.assoc, relativeEquivalencePathMapAt_snd,
      equivalencePathMap_endpoint]

/-- 可換四角形の縦射が単射なら、相対 path の標的の比較も単射。 -/
instance relativePathSquareTargetMap_mono {A B X Y : SSet.{u}} (p : A ⟶ B) (q : X ⟶ Y)
    (a : A ⟶ X) (b : B ⟶ Y) (h : p ≫ b = a ≫ q) (j : Fin 2) [Mono a] [Mono b] :
    Mono (relativePathSquareTargetMap p q a b h j) := by
  constructor
  intro Z f g he
  apply pullback.hom_ext
  · apply (cancel_mono (equivalencePathMap b)).mp
    have ht := congrArg
      (fun m : Z ⟶ relativeEquivalencePathTargetAt q j ↦
        m ≫ pullback.fst (equivalencePathEndpoint Y j) q) he
    simpa only [Category.assoc, relativePathSquareTargetMap_fst] using ht
  · apply (cancel_mono a).mp
    have ht := congrArg
      (fun m : Z ⟶ relativeEquivalencePathTargetAt q j ↦
        m ≫ pullback.snd (equivalencePathEndpoint Y j) q) he
    simpa only [Category.assoc, relativePathSquareTargetMap_snd] using ht

end SerrePositivity.InfinityCategories
