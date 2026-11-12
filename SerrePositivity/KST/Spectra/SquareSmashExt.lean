module

public import SerrePositivity.KST.Spectra.SquareReducedDesc
public import Mathlib.CategoryTheory.Functor.EpiMono

/-!
概要：二つの円の smash 積からの写像を正方形上で判定する。
方針：円の商射の全射性と smash の商の普遍性を使う。
規約：Kan 性は要求しない。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。三角形分割との比較の一意性。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：単体的な円の商射は全射である。
方針：境界の頂点から単位への射が分裂全射であり、その pushout を取る。
規約：境界を潰す標準の円を使う。
使われ方：Goerss–Jardine I §7。正方形上での等式による商の写像の判定。 -/
instance circleQuotient_epi : Epi (PointedObject.cofiberQuotient (boundary.{u} 1).ι) := by
  have : Epi (toUnit (boundary.{u} 1 : SSet.{u})) := by
    refine ⟨?_⟩
    intro Z f g h
    let s : 𝟙_ SSet.{u} ⟶ (boundary.{u} 1 : SSet.{u}) :=
      stdSimplex.isTerminalObj₀.from _ ≫ boundary.ι (0 : Fin 2)
    have h' := congrArg (fun k => s ≫ k) h
    simpa only [← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp] using h'
  exact (SphereSimplex.quotient_isPushout 1).epi_inl_of_epi

/-- 概要：二つの円の商射の積も全射である。
方針：閉構造の積関手による全射の保存を使う。
規約：二つの区間から二つの円への積の射。
使われ方：Kerodon §3.2.3（Tag 00W3）。二変数の商における等式の判定。 -/
instance squareCircleQuotient_epi : Epi
    (PointedObject.cofiberQuotient (boundary.{u} 1).ι ⊗ₘ
      PointedObject.cofiberQuotient (boundary.{u} 1).ι) := by
  rw [tensorHom_def]
  have : Epi (PointedObject.cofiberQuotient (boundary.{u} 1).ι ▷ (Δ[1] : SSet.{u})) :=
    Functor.map_epi (tensorRight (Δ[1] : SSet.{u})) _
  have : Epi ((PointedObject.cofiber (boundary.{u} 1).ι).right ◁
      PointedObject.cofiberQuotient (boundary.{u} 1).ι) :=
    Functor.map_epi (tensorLeft (PointedObject.cofiber (boundary.{u} 1).ι).right) _
  infer_instance

/-- 概要：二つの円の smash 積からの射は正方形上で判定できる。
方針：smash の商で判定し、円の商射の積の全射性で打ち消す。
規約：正方形からの射は二つの商射と smash の商射の合成。
使われ方：Goerss–Jardine I §7。相対三角形の貼り合わせとの比較の一意性。 -/
theorem squareSmash_hom_ext {Y : PointedSimplicialSet.{u}}
    {f g : PointedObject.smash PointedSimplicialSet.circle.{u}
      PointedSimplicialSet.circle.{u} ⟶ Y}
    (h : (PointedObject.cofiberQuotient (boundary.{u} 1).ι ⊗ₘ
        PointedObject.cofiberQuotient (boundary.{u} 1).ι) ≫
          (PointedObject.smashQuotient PointedSimplicialSet.circle.{u}
            PointedSimplicialSet.circle.{u}).right ≫ f.right =
      (PointedObject.cofiberQuotient (boundary.{u} 1).ι ⊗ₘ
        PointedObject.cofiberQuotient (boundary.{u} 1).ι) ≫
          (PointedObject.smashQuotient PointedSimplicialSet.circle.{u}
            PointedSimplicialSet.circle.{u}).right ≫ g.right) : f = g := by
  apply PointedObject.smash_hom_ext
  apply Under.UnderMorphism.ext
  exact (cancel_epi (PointedObject.cofiberQuotient (boundary.{u} 1).ι ⊗ₘ
    PointedObject.cofiberQuotient (boundary.{u} 1).ι)).mp h

end

end SerrePositivity.KST.Spectra
