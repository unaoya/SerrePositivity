module

public import SerrePositivity.KST.Descent.ReductionFunctor
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Noether スキームの被約化と冪零不変性

## 概要
有限アフィン被覆上の冪零指数を統一し、Noether スキームの reduction が
実際に冪零 thickening であることを証明する。

## 方針
準コンパクト性で有限アフィン被覆を選び、各切断環の nilradical の指数の最大値を取る。
イデアル層の等式を被覆上で検査する。

## 規約
局所 Noether 性だけでは一様な指数を主張せず、準コンパクト性も使う。
前層の不変性は公理 (3) の明示的な引数から適用する。

## 使われ方
論文 補題 3.3 と定理 3.1 の「一般 → 被約」の還元。
-/

@[expose] public section

universe u w t

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace SerrePositivity.KST.Descent

/-- 概要：Noether な基底上有限型の対象は Noether スキーム（論文 §3）。
方針：局所有限型性で局所 Noether 性を移し、準コンパクト性で有限被覆を保証する。
規約：基底の Noether 性を明示し、一般の基底には主張しない。
使われ方：有限型の圏の全対象に対する reduction の冪零性。 -/
instance finiteTypeScheme_isNoetherian {S : Scheme.{u}} [IsNoetherian S]
    (X : FiniteTypeSchemes S) : IsNoetherian X.obj.left := by
  have : LocallyOfFiniteType X.obj.hom := X.property.1
  have : QuasiCompact X.obj.hom := X.property.2
  have := LocallyOfFiniteType.isLocallyNoetherian X.obj.hom
  have := QuasiCompact.compactSpace_of_compactSpace X.obj.hom
  exact ⟨⟩

/-- 概要：有限アフィン被覆上で冪零なイデアル層は大域的に冪零（論文 §3）。
方針：局所指数の最大値を取り、被覆上でその冪が零であることを検査する。
規約：被覆の有限性は一様な指数の構成に用いる。
使われ方：reduction の核の冪零性。 -/
theorem idealSheaf_isNilpotent_of_finite_affine_cover {X : Scheme.{u}}
    {ι : Type*} [Finite ι] (U : ι → X.affineOpens)
    (cover : ⨆ i, (U i).1 = ⊤) (I : X.IdealSheafData)
    (local_nilpotent : ∀ i, IsNilpotent (I.ideal (U i))) : IsNilpotent I := by
  classical
  let := Fintype.ofFinite ι
  choose n hn using local_nilpotent
  refine ⟨Finset.univ.sup n, Scheme.IdealSheafData.ext_of_iSup_eq_top U cover ?_⟩
  intro i
  change I.ideal (U i) ^ Finset.univ.sup n = 0
  exact pow_eq_zero_of_le (Finset.le_sup (Finset.mem_univ i)) (hn i)

/-- 概要：Noether スキームの nilradical イデアル層は冪零（論文 §3）。
方針：全アフィン開被覆から有限部分被覆を選び、各 Noether 切断環の冪零性を貼る。
規約：被覆の外で指数を仮定することなく、有限個の指数から構成する。
使われ方：非アフィンの reduction に公理 (3) を適用する幾何条件。 -/
theorem noetherian_nilradical_isNilpotent (X : Scheme.{u}) [IsNoetherian X] :
    IsNilpotent X.nilradical := by
  classical
  have cover : (Set.univ : Set X) ⊆ ⋃ U : X.affineOpens, (U.1 : Set X) := by
    rw [← Opens.coe_iSup, iSup_affineOpens_eq_top]
    exact Set.Subset.refl _
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens ↦ (U.1 : Set X)) (fun U ↦ U.1.isOpen) cover
  have finite_cover : ⨆ U : s, (U.val.1 : X.Opens) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨U, hx⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ x))
    obtain ⟨hU, hx⟩ := Set.mem_iUnion.mp hx
    exact Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hx⟩
  apply idealSheaf_isNilpotent_of_finite_affine_cover (fun U : s ↦ U.val) finite_cover
  intro U
  have := IsLocallyNoetherian.component_noetherian U.val
  change IsNilpotent (nilradical Γ(X, U.val))
  exact IsNoetherianRing.isNilpotent_nilradical _

/-- 概要：Noether スキームの reduction の包含は冪零 thickening（論文 §3）。
方針：包含の核の同定と、有限被覆から構成した大域的な冪零性を使う。
規約：アフィン性を要求しない。
使われ方：一般から被約への還元の指定射。 -/
instance noetherianReduction_isNilpotentThickening (X : Scheme.{u}) [IsNoetherian X] :
    IsNilpotentThickening (schemeReductionInclusion X) where
  nilpotent_ker := by
    rw [schemeReductionInclusion_ker]
    exact noetherian_nilradical_isNilpotent X

/-- 概要：Noether な有限型対象の被約化の引き戻しは全次数同型（論文 定理 3.1）。
方針：被約化の包含の冪零性を証明して公理 (3) に入力する。
規約：任意の係数と整数次数について、実際の包含の引き戻しを比較する。
使われ方：定理 3.1 の「一般 → 被約」の前層に関する還元。 -/
theorem Nilinvariant.noetherianReduction_pullback_bijective {S : Scheme.{u}}
    {Coefficient : Type w}
    (L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient) [Nilinvariant S L]
    (X : FiniteTypeSchemes S) [IsNoetherian X.obj.left] (H : Coefficient) (n : ℤ) :
    Function.Bijective (L.pullback H n (reducedClosedAsFiniteTypeInclusion X ⊤)) := by
  have : IsNilpotentThickening (reducedClosedAsFiniteTypeInclusion X ⊤).hom.left :=
    noetherianReduction_isNilpotentThickening X.obj.left
  exact Nilinvariant.pullback_bijective (S := S) (L := L)
    (reducedClosedAsFiniteTypeInclusion X ⊤) H n

end SerrePositivity.KST.Descent
