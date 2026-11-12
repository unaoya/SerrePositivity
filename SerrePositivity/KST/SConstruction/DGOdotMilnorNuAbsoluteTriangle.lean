module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullTriangleFactor

/-!
概要：同じ完備化付き絶対提示の元零化三角形と最大合成を保持する。
方針：元の実 Verdier 提示の零角を経由する上三角形をそのまま読む。
規約：元の選択提示を変更しない。使われ方：固定 ν 実面との全 Hom 比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：同じ完備化付き絶対提示の元上下二単体。
方針：元の実 raw 四角形を元の三角形に制限する。
規約：別の充填を選ばない。使われ方：実面との相対比較の絶対側。 -/
def dgOdotMilnorNuAbsoluteNullTriangle (j : Fin 2) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} _⦋2⦌ :=
  SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle j ≫
    perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h))

/-- 概要：絶対上三角形の元対象を豊穣安定圏に保持する。
方針：元二単体の対象写像を読む。
規約：元の三頂点。使われ方：同じ全 Hom の型付け。 -/
abbrev dgOdotMilnorNuAbsoluteTriangleStableObject (i : Fin 3) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1} :=
  (dgOdotMilnorNuAbsoluteNullTriangle R d h 0).obj ⟨ULift.up i⟩
local notation "σ" => dgOdotMilnorNuAbsoluteNullTriangle R d h 0
local notation "X₀" => dgOdotMilnorNuAbsoluteTriangleStableObject R d h 0
local notation "X₁" => dgOdotMilnorNuAbsoluteTriangleStableObject R d h 1
local notation "X₂" => dgOdotMilnorNuAbsoluteTriangleStableObject R d h 2

/-- 概要：同じ絶対上三角形の中間対象は元の零角。
方針：元提示の四角の頂点式と同じ三角形の中間頂点を照合する。
規約：元の零圏を保持。使われ方：実最大合成の零性。 -/
lemma dgOdotMilnorNuAbsoluteTriangle_middle_zero : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (X₁) := by
  let F : (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} :=
    perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h)
  let t := SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u + 2} 0)
  have hn := NatTrans.naturality_apply F
    (SimplexCategory.const ⦋0⦌ ⦋2⦌ (1 : Fin 3)).op t
  have hs : (Δ[1] ⊗ Δ[1] : SSet.{u + 2}).map
      (SimplexCategory.const ⦋0⦌ ⦋2⦌ (1 : Fin 3)).op t =
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2),
          stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
    apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl
  have he : (X₁) = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 1) := by
    have hn' := congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject hn
    rw [hs] at hn'
    exact hn'.symm
  rw [he, (perfectVerdierRawSquare_vertices (dgOdotMilnorNuPerfectSequence R d h)).2.2.2,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject_vertex]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory_isZero

/-- 概要：同じ絶対上三角形の元最大 path の合成完全射。
方針：元の全 Hom 作用の通常射を取る。
規約：元合成を保持。使われ方：絶対側の終関手零成分の基準頂点。 -/
def dgOdotMilnorNuAbsoluteTriangleMaximalComposite : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (X₀) (X₂) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (σ)).map dgOdotMilnorNuNullUpperMaximalPath.{u}

/-- 概要：同じ絶対最大合成は全対象を零対象へ送る。
方針：元最大 path を二隣接 path に分解し、元零角の全零性を使う。
規約：指定二単体を選び直さない。使われ方：同じ絶対全 Hom の零成分判定。 -/
lemma dgOdotMilnorNuAbsoluteTriangleMaximalComposite_zero (x : (X₀).obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((dgOdotMilnorNuAbsoluteTriangleMaximalComposite R d h).hom.app
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
  have hpq : dgOdotMilnorNuNullUpperMaximalPath.{u} = p ≫ q :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentMaximalPathFunctor (ULift.{u + 1} (Fin 3))).map_comp
      (homOfLE (show (ULift.up (0 : Fin 3) : ULift.{u + 1} (Fin 3)) ≤ ULift.up 1 by decide))
      (homOfLE (show (ULift.up (1 : Fin 3) : ULift.{u + 1} (Fin 3)) ≤ ULift.up 2 by decide))
  have he := congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.hom (F.map_comp p q)
  change (F.map (p ≫ q)).hom = f.hom ≫ g.hom at he
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((F.map dgOdotMilnorNuNullUpperMaximalPath.{u}).hom.app
    (Opposite.op ⦋0⦌) x)
  rw [hpq, he]
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (g.hom.app _ (f.hom.app _ x))
  exact @_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero _ _ g.hom g.isExact _
    (dgOdotMilnorNuAbsoluteTriangle_middle_zero R d h _)

end SerrePositivity.KST.SConstruction
