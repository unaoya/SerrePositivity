module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedSectionsUniverseHomEquiv

/-!
概要：元の指定した重み付き切断空間の宇宙比較射が実同型であることを示す。
方針：同じHom全単射を標準単体に適用し、Yonedaによって元の比較射の各成分と照合する。
規約：IS-W2 R02〜R03の係数移送の法則。順射を選び直さない。
使われ方：同じBK切断の宇宙変更と標準脚の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open scoped Simplicial
variable (I : Type u) [SmallCategory I] (W H : I ⥤ SSet.{u})

/-- 元の標準単体のHom全単射による、同じ切断の各次数の全単射。 -/
def weightedSectionsUniverseSimplexEquiv (n : ℕ) :
    ((SSet.uliftFunctor.{max u v,u}).obj (weightedSections W H)) _⦋n⦌ ≃
      (weightedSections ((weightedDiagramUniverse.{u,v} I).obj W)
        ((weightedDiagramUniverse.{u,v} I).obj H)) _⦋n⦌ :=
  Equiv.ulift.trans (SSet.yonedaEquiv.symm.trans
    ((weightedSectionsUniverseHomEquiv I W H Δ[n]).trans
      (((uliftStdSimplexIso.{u,max u v} n).homCongr (Iso.refl _)).trans SSet.yonedaEquiv)))

/-- 各次数の全単射の順写像は、元の指定比較射の成分そのもの。 -/
theorem weightedSectionsUniverseSimplexEquiv_apply {n : ℕ}
    (s : ((SSet.uliftFunctor.{max u v,u}).obj (weightedSections W H)) _⦋n⦌) :
    weightedSectionsUniverseSimplexEquiv I W H n s =
      (weightedSectionsUniverseComparison.{u,v} I W H).app (Opposite.op ⦋n⦌) s := by
  change SSet.yonedaEquiv ((uliftStdSimplexIso.{u,max u v} n).inv ≫
    (((SSet.uliftFunctor.{max u v,u}).map (SSet.yonedaEquiv.symm s.down) ≫
      weightedSectionsUniverseComparison I W H) ≫ 𝟙 _)) = _
  rw [Category.comp_id, ← Category.assoc, uliftYonedaMap,
    SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  cases s
  rfl

/-- 元の指定した切断空間の宇宙比較射は、全次数で可逆。 -/
instance weightedSectionsUniverseComparison_isIso :
    IsIso (weightedSectionsUniverseComparison.{u,v} I W H) := by
  rw [NatTrans.isIso_iff_isIso_app]
  rintro ⟨⟨n⟩⟩
  rw [isIso_iff_bijective]
  change Function.Bijective (fun s => (weightedSectionsUniverseComparison I W H).app _ s)
  have h : (fun s => (weightedSectionsUniverseComparison I W H).app (Opposite.op ⦋n⦌) s) =
      weightedSectionsUniverseSimplexEquiv I W H n :=
    funext (fun s => (weightedSectionsUniverseSimplexEquiv_apply I W H s).symm)
  rw [h]
  exact (weightedSectionsUniverseSimplexEquiv I W H n).bijective

/-- 元の比較を順射とする、同じ重み付き切断の指定宇宙変更同型。 -/
def weightedSectionsUniverseIso :
    (SSet.uliftFunctor.{max u v,u}).obj (weightedSections W H) ≅
      weightedSections ((weightedDiagramUniverse.{u,v} I).obj W)
        ((weightedDiagramUniverse.{u,v} I).obj H) :=
  asIso (weightedSectionsUniverseComparison I W H)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
