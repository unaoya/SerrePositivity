module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveCylinderBoundary
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveMovingParameterRelative

/-!
# 中断した任意モデル源への一般化：NerveCylinderExtension

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Relative moving extension retaining both whole cylinder boundary systems。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0469][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0469
[plan]: ../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Relative moving extension retaining both whole cylinder boundary systems
-/

@[expose] public section
universe w v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open SerrePositivity.Reedy

namespace SerrePositivity.SimplicialModel.NerveCylinderExtension
open NerveCylinderBoundary
variable {D : Type uD} [Category.{vD} D]
  (V K : D ⥤ SSet.{max w v}) (i : V ⟶ K)
  {A T : SSet.{max w v}} (j : A ⟶ T) (F : D ⥤ SSet.{v})
  (hi : ∀ d, Mono (i.app d)) [Mono j]
  (hp : ∀ d, UniverseLift.BoundaryFillers (F.obj d))
  (b : NerveMovingParameter.System (product K A) F)
  (c : NerveMovingParameter.System (product V T) F)
  (h : b ≫ NerveBiparameterMaps.restriction _ _ (NerveMovingParameter.lifted F)
      (horizontal V K i A) =
    c ≫ NerveBiparameterMaps.restriction _ _ (NerveMovingParameter.lifted F) (vertical j V))
  (n : ℕ) (old : NerveMovingParameter.LowerSystem (product K T) F n)
  (hboundary : old ≫ Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n)
      (NerveMovingParameterRelative.restriction (boundary V K i j) (product K T)
        (inclusion V K i j) F) =
    Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n)
      (system V K i j (NerveMovingParameter.lifted F) b c h))

/-- The prescribed lower system can contain entire old interval families at each center. -/
def extend : NerveMovingParameter.System (product K T) F :=
  NerveMovingParameterRelative.extend (boundary V K i j) (product K T)
    (inclusion V K i j) F hp (inclusion_mono V K i j hi)
    (system V K i j (NerveMovingParameter.lifted F) b c h) n old hboundary

lemma extend_boundary : extend V K i j F hi hp b c h n old hboundary ≫
    NerveMovingParameterRelative.restriction (boundary V K i j) (product K T)
      (inclusion V K i j) F =
    system V K i j (NerveMovingParameter.lifted F) b c h :=
  NerveMovingParameterRelative.extend_boundary _ _ _ _ _ _ _ _ _ _

lemma extend_restrict : Functor.whiskerLeft
    (lowerInclusion (NerveCoherentFamily.reedy D) n)
      (extend V K i j F hi hp b c h n old hboundary) = old :=
  NerveMovingParameterRelative.extend_restrict _ _ _ _ _ _ _ _ _ _

lemma extend_piece (P : D ⥤ SSet.{max w v}) (k : P ⟶ boundary V K i j) :
    extend V K i j F hi hp b c h n old hboundary ≫
      NerveBiparameterMaps.restriction P (product K T) (NerveMovingParameter.lifted F)
        (k ≫ inclusion V K i j) =
    system V K i j (NerveMovingParameter.lifted F) b c h ≫
      NerveBiparameterMaps.restriction P (boundary V K i j) (NerveMovingParameter.lifted F) k := by
  rw [← NerveBiparameterMaps.restriction_comp, ← Category.assoc]
  exact congrArg (fun z => z ≫ NerveBiparameterMaps.restriction P (boundary V K i j)
    (NerveMovingParameter.lifted F) k)
      (extend_boundary V K i j F hi hp b c h n old hboundary)

/-- Retain the prescribed endpoint system in every external degree. -/
lemma extend_endpoints : extend V K i j F hi hp b c h n old hboundary ≫
    NerveBiparameterMaps.restriction _ _ (NerveMovingParameter.lifted F) (vertical j K) = b := by
  rw [← endpointInclusion_inclusion V K i j]
  exact (extend_piece V K i j F hi hp b c h n old hboundary _
    (endpointInclusion V K i j)).trans (system_endpoints V K i j _ b c h)

/-- Retain the whole vertex cylinder system in every external degree. -/
lemma extend_vertices : extend V K i j F hi hp b c h n old hboundary ≫
    NerveBiparameterMaps.restriction _ _ (NerveMovingParameter.lifted F)
      (horizontal V K i T) = c := by
  rw [← vertexInclusion_inclusion V K i j]
  exact (extend_piece V K i j F hi hp b c h n old hboundary _
    (vertexInclusion V K i j)).trans (system_vertices V K i j _ b c h)

end SerrePositivity.SimplicialModel.NerveCylinderExtension
