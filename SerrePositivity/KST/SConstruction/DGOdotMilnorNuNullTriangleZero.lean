module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullTriangle
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.MaximalPathFunctor
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderPostcomposition

/-!
概要：元の実零化三角形の最大 path の合成が全零であることを確認する。
方針：同じ豊穣二単体の通常関手を使い、実零角を経由して分解する。
規約：二単体自体を置換せず、元の Hom 作用の値を使う。
使われ方：実三角形の全 Hom データを可縮な零合成空間へ置く。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "σ" => dgOdotMilnorNuNullTriangle R d 0
/-- 概要：元の実零化二単体の各対象を豊穣安定圏の対象として保持する。
方針：元の同じ二単体の対象写像を読む。
規約：安定圏と core 豊穣圏の instance を区別する。使われ方：実 Hom の型照合。 -/
abbrev dgOdotMilnorNuNullTriangleStableObject (i : Fin 3) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1} :=
  (dgOdotMilnorNuNullTriangle R d 0).obj ⟨ULift.up i⟩
local notation "X₀" => dgOdotMilnorNuNullTriangleStableObject R d 0
local notation "X₁" => dgOdotMilnorNuNullTriangleStableObject R d 1
local notation "X₂" => dgOdotMilnorNuNullTriangleStableObject R d 2

/-- 概要：実零化二単体の最大 path に沿う元の合成完全射。
方針：同じ豊穣関手の通常射への作用を使用する。
規約：指定二単体の Hom 作用を保持する。使われ方：全零 Hom 成分の基準頂点。 -/
def dgOdotMilnorNuNullTriangleMaximalComposite : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (X₀) (X₂) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (σ)).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentMaximalPath
      (show (ULift.up (0 : Fin 3) : ULift.{u + 1} (Fin 3)) ≤ ULift.up 2 by decide))

/-- 概要：同じ最大 path の実合成は全対象を零対象へ送る。
方針：最大 path を二つの隣接 path に分解し、実零角の零性を使う。
規約：新しい合成二単体を選択しない。使われ方：元の二単体の Hom 成分の零性。 -/
lemma dgOdotMilnorNuNullTriangleMaximalComposite_zero (x : (X₀).obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((dgOdotMilnorNuNullTriangleMaximalComposite R d).hom.app
      (Opposite.op ⦋0⦌) x) := by
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (σ)
  let p : (⟨ULift.up (0 : Fin 3)⟩ :
      SimplicialThickening (ULift.{u + 1} (Fin 3))) ⟶ ⟨ULift.up (1 : Fin 3)⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentMaximalPath (show (ULift.up (0 : Fin 3) : ULift.{u + 1} (Fin 3)) ≤ ULift.up 1 by decide)
  let q : (⟨ULift.up (1 : Fin 3)⟩ :
      SimplicialThickening (ULift.{u + 1} (Fin 3))) ⟶ ⟨ULift.up (2 : Fin 3)⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentMaximalPath (show (ULift.up (1 : Fin 3) : ULift.{u + 1} (Fin 3)) ≤ ULift.up 2 by decide)
  let f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (X₀) (X₁) := F.map p
  let g : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (X₁) (X₂) := F.map q
  have hpq : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentMaximalPath
      (show (ULift.up (0 : Fin 3) : ULift.{u + 1} (Fin 3)) ≤ ULift.up 2 by decide) = p ≫ q :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentMaximalPathFunctor (ULift.{u + 1} (Fin 3))).map_comp
      (homOfLE (show (ULift.up (0 : Fin 3) : ULift.{u + 1} (Fin 3)) ≤ ULift.up 1 by decide))
      (homOfLE (show (ULift.up (1 : Fin 3) : ULift.{u + 1} (Fin 3)) ≤ ULift.up 2 by decide))
  have he := congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.hom (F.map_comp p q)
  change (F.map (p ≫ q)).hom = f.hom ≫ g.hom at he
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((F.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentMaximalPath
    (show (ULift.up (0 : Fin 3) : ULift.{u + 1} (Fin 3)) ≤ ULift.up 2 by decide))).hom.app
      (Opposite.op ⦋0⦌) x)
  rw [hpq, he]
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (g.hom.app _ (f.hom.app _ x))
  exact @_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero _ _ g.hom g.isExact _
    (dgOdotMilnorNuNullTriangle_middle_zero R d _)

end SerrePositivity.KST.SConstruction
