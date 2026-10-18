module

public import SerrePositivity.KST.Comparison.FatFreeColumnsIso
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalLocalizedEquivalence

/-!
# fat realization と対角の自然な比較の局所化可逆性

概要：実際の fat realization から対角への自然な射は局所化同型である。
方針：列ごとの自由な退化の augmentation と対角の保存定理を使い、標準形で比較射を同定する。
規約：Segal 1974 Proposition 1.6 の模型比較。自由な退化の標準単体上の実際の収縮から証明する経路。
使われ方：fat realization 版のホモトピー引き戻しを対角版へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite
open SerrePositivity.BisimplicialModel SerrePositivity.SimplicialModel

/--
概要：対角への比較は全射な標準形をその全射による外側の作用で評価する。
方針：比較の各行の式を代表に適用する。
規約：行の元の内側次数は変えない。
使われ方：列の augmentation と元の自然な比較の一致。
-/
theorem fatRealizationToDiagonal_realize (F : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    (d : SimplexCategoryᵒᵖ) (p : FatNormalForm F d) :
    (fatRealizationToDiagonal F).app d (fatNormalFormRealize F d p) =
      (F.map p.epi.op).app d p.simplex := by
  have h := congrArg (fun t => t.app d (p.simplex, SSet.stdSimplex.objEquiv.symm p.epi))
    (fatRealizationInclusion_toDiagonal F p.degree.len)
  change (fatRealizationToDiagonal F).app d (fatNormalFormRealize F d p) =
    (F.map (SSet.stdSimplex.objEquiv.{u} (SSet.stdSimplex.objEquiv.{u}.symm p.epi)).op).app d
      p.simplex at h
  rw [Equiv.apply_symm_apply] at h
  exact h

/--
概要：列の augmentation の対角による比較は元の fat realization の比較と一致する。
方針：各元を全射な標準形で表し、双方の評価の式を計算する。
規約：全ての同型は局所化前の実際の射。
使われ方：元の比較射の局所化可逆性。
-/
theorem fatFreeColumnsIso_augmentation (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (fatFreeColumnsIso F).hom ≫ diagonal.map (freeColumnsAugmentation F) ≫
      (diagonalFlipIso F).hom = fatRealizationToDiagonal F := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro x
  obtain ⟨p, rfl⟩ := (fatNormalFormEquiv F d).symm.surjective x
  change (freeDegeneraciesAugmentation.app (F.flip.obj d)).app d
    (fatNormalFormRealize _ _ (fatColumnNormalFormEquiv F d
      (fatDegreeNormalize F d (fatNormalFormRealize F d p)))) =
    (fatRealizationToDiagonal F).app d (fatNormalFormRealize F d p)
  rw [fatDegreeNormalize_realize, freeDegeneraciesAugmentation_realize,
    fatRealizationToDiagonal_realize]
  rfl

/--
概要：fat realization から対角への自然な比較は局所化同型である。
方針：各列の自由な退化の augmentation が局所化同型であることを対角へ送り、比較の一致を使う。
規約：二重単体集合の Kan 性や面の条件は不要。
使われ方：Segal Proposition 1.6 の対角版。
-/
theorem fatRealizationToDiagonal_localized_isIso (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (fatRealizationToDiagonal F)) := by
  have h : IsIso (AnodyneHomotopy.anodyneQ.map (diagonal.map (freeColumnsAugmentation F))) :=
    localized_diagonal_map (freeColumnsAugmentation F)
      (fun d => freeDegeneraciesAugmentation_localized_isIso (F.flip.obj d))
  rw [← fatFreeColumnsIso_augmentation, Functor.map_comp, Functor.map_comp]
  infer_instance

end SerrePositivity.KST.Comparison
