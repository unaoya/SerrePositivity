module

public import SerrePositivity.KST.Descent.FiniteTypeLimitPreservation
public import SerrePositivity.KST.Descent.FiniteTypeUniversal
public import Mathlib.CategoryTheory.Extensive

/-!
# 有限型の圏の任意の有限非交和

## 概要
Noether 基底上で異なる有限型対象の有限非交和を構成し、指定包含の普遍性を証明する。

## 方針
スキームの標準非交和の構造射を使い、有限型性と有限非交和の準コンパクト性を検査する。

## 規約
有限個の対象は同じ基底上にある。無限非交和を有限型とは主張しない。

## 使われ方
論文 補題 3.2 の有限個の局所自由 chart と変動 rank の成分、(3.8) の有限非交和。
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} [IsNoetherian S]
  {I : Type v} [Finite I] (X : I → FiniteTypeSchemes S)

/-- 概要：異なる有限型対象の実際の有限非交和（補題 3.2、(3.8)）。
方針：標準非交和の構造射は局所有限型、始域は局所 Noether かつ有限非交和で準コンパクト。
規約：underlying scheme は標準の非交和。使われ方：局所自由 chart の全体を一つの有限型射にする。 -/
def finiteTypeCoproduct : FiniteTypeSchemes S := by
  let : IsZariskiLocalAtSource (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType.{u})
  have hloc : LocallyOfFiniteType (Sigma.desc (fun i ↦ (X i).obj.hom)) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFiniteType.{u}) (fun i ↦ (X i).property.1)
  have : IsLocallyNoetherian (∐ fun i ↦ (X i).obj.left) :=
    LocallyOfFiniteType.isLocallyNoetherian (Sigma.desc (fun i ↦ (X i).obj.hom))
  have : ∀ i, CompactSpace (X i).obj.left := fun _ ↦ inferInstance
  let cov := sigmaOpenCover (fun i ↦ (X i).obj.left)
  have : Finite cov.I₀ := by change Finite I; infer_instance
  have : ∀ i, CompactSpace (cov.X i) := by
    intro i
    change CompactSpace (X i).obj.left
    infer_instance
  have : CompactSpace ((∐ fun i ↦ (X i).obj.left) : Scheme.{u}) :=
    Scheme.OpenCover.compactSpace cov
  have : IsNoetherian (∐ fun i ↦ (X i).obj.left) := ⟨⟩
  have hqc : QuasiCompact (Sigma.desc (fun i ↦ (X i).obj.hom)) :=
    quasiCompact_of_noetherianSpace_source _
  exact ⟨Over.mk (Sigma.desc (fun i ↦ (X i).obj.hom)), hloc, hqc⟩

/-- 概要：有限型の各成分から非交和への実際の指定包含（補題 3.2、(3.8)）。
方針：標準の包含を基底上の射へ持ち上げる。
規約：元の包含を変更しない。使われ方：前層の各成分での検査。 -/
def finiteTypeCoproductInclusion (i : I) : X i ⟶ finiteTypeCoproduct X :=
  ObjectProperty.homMk (Over.homMk (Sigma.ι (fun i ↦ (X i).obj.left) i)
    (Sigma.ι_comp_desc _ i))

/-- 概要：構成した有限非交和と指定包含は元の有限型の圏内で普遍（補題 3.2、(3.8)）。
方針：スキームの標準非交和の普遍性を Over と充満部分圏で反映する。
規約：異なる有限型対象を許す。使われ方：反対圏の有限積を保つ前層への適用。 -/
def finiteTypeCoproductIsColimit :
    IsColimit (Cofan.mk (finiteTypeCoproduct X) (finiteTypeCoproductInclusion X)) :=
  finiteTypeCofanIsColimitOfSchemeIsColimit (finiteTypeCoproductInclusion X)
    (coproductIsCoproduct (fun i ↦ (X i).obj.left))

/-- 概要：Noether 基底上の有限型の圏には全ての有限非交和が存在（補題 3.2）。
方針：実際の構成と指定包含の普遍性を HasColimit へ束ねる。
規約：空の非交和も含む。使われ方：有限非交和の底変換の幾何。 -/
instance finiteTypeSchemes_hasFiniteCoproducts : HasFiniteCoproducts (FiniteTypeSchemes S) where
  out n := ⟨fun F ↦ by
    let X : Fin n → FiniteTypeSchemes S := fun j ↦ F.obj ⟨j⟩
    have e : Discrete.functor X ≅ F := Discrete.natIso (fun _ ↦ Iso.refl _)
    let : HasColimit (Discrete.functor X) :=
      HasColimit.mk ⟨_, finiteTypeCoproductIsColimit X⟩
    exact hasColimit_of_iso e.symm⟩

/-- 概要：スキームへの忘却は有限型の圏の実際の有限非交和を保存（補題 3.2、(3.8)）。
方針：構成した標準非交和の余錐を忘却するとスキームの指定余錐になる。
規約：任意の有限個の異なる対象を扱う。使われ方：非交和の底変換の普遍性の反映。 -/
instance finiteTypeSchemesForget_preservesFiniteCoproducts (J : Type v) [Finite J] :
    PreservesColimitsOfShape (Discrete J) (finiteTypeSchemesForget S) := by
  let F := finiteTypeSchemesForget S
  have : ∀ X : J → FiniteTypeSchemes S, PreservesColimit (Discrete.functor X) F := fun X ↦
    preservesColimit_of_preserves_colimit_cocone (finiteTypeCoproductIsColimit X)
      ((isColimitMapCoconeCofanMkEquiv F X (finiteTypeCoproductInclusion X)).symm
        (coproductIsCoproduct (fun i ↦ (X i).obj.left)))
  exact preservesColimitsOfShape_of_discrete F

/-- 概要：有限型の圏からスキームへの忘却は同型を反映（補題 3.2）。
方針：充満部分圏の包含と Over の忘却を合成する。
規約：元の基底上の射の同型を反映する。使われ方：有限非交和の extensive 性の移送。 -/
instance finiteTypeSchemesForget_reflectsIsomorphisms :
    (finiteTypeSchemesForget S).ReflectsIsomorphisms := by
  change (finiteTypeOverInclusion S ⋙ Over.forget S).ReflectsIsomorphisms
  infer_instance

/-- 概要：Noether 基底上の有限型の圏は有限の非交和に関して extensive（補題 3.2）。
方針：有限非交和と引き戻しを保ち同型を反映する忘却から、スキームの extensive 性を移す。
規約：無限非交和は含まない。使われ方：Čech 段の零番目の座標で有限成分を引き戻す。 -/
instance finiteTypeSchemes_finitaryExtensive : FinitaryExtensive (FiniteTypeSchemes S) :=
  CategoryTheory.finitaryExtensive_of_preserves_and_reflects_isomorphism (finiteTypeSchemesForget S)

end SerrePositivity.KST.Descent
