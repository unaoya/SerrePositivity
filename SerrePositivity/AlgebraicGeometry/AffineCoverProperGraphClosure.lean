module

public import SerrePositivity.AlgebraicGeometry.SchemeDenseAffineCoverModel
public import SerrePositivity.AlgebraicGeometry.AffineSchemeProperAmbient
public import SerrePositivity.AlgebraicGeometry.ProperGraphClosure

/-!
概要：実際の稠密な affine 被覆模型から固有なグラフ閉包を供給する。
方針：各 affine チャートの有限型の構造射に固有な周辺を取り、共通の開をまとめる。
規約：チャートと射影の可換式を保持する。
使われ方：C06 の各チャートへの射影の因子化と貼り合わせ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 稠密な affine 被覆模型の実際のチャートから、固有なグラフ閉包を供給する。 -/
theorem exists_affine_cover_proper_graph_closure {X S : Scheme.{u}}
    (D : SchemeDenseAffineCoverModel X) [IsAffine S]
    (f : X ⟶ S) [LocallyOfFiniteType f] :
    ∃ (P : Fin D.n → Scheme.{u}) (p : ∀ i, P i ⟶ S)
      (e : ∀ i, (D.chart i).toScheme ⟶ P i)
      (Z : Scheme.{u}) (j : D.common ⟶ Z) (q : Z ⟶ S) (π : ∀ i, Z ⟶ P i),
      (∀ i, IsProper (p i)) ∧ (∀ i, IsImmersion (e i)) ∧
      (∀ i, e i ≫ p i = (D.chart i).ι ≫ D.toBase ≫ f) ∧
      IsOpenImmersion j ∧ IsSchemeTheoreticallyDominant j ∧ IsProper q ∧
      (∀ i, IsProper (π i)) ∧ j ≫ q = D.commonι ≫ D.toBase ≫ f ∧
      (∀ i, π i ≫ p i = q) ∧ ∀ i, j ≫ π i = D.toChart i ≫ e i := by
  classical
  letI : IsNoetherian D.base := D.base_noetherian
  letI : IsNoetherian D.common := D.common_noetherian
  letI : IsClosedImmersion D.toBase := D.toBase_closed
  have h (i : Fin D.n) : ∃ (P : Scheme.{u}) (p : P ⟶ S)
      (e : (D.chart i).toScheme ⟶ P),
      IsProper p ∧ IsImmersion e ∧ e ≫ p = (D.chart i).ι ≫ D.toBase ≫ f := by
    letI : IsAffine (D.chart i).toScheme := D.chart_affine i
    exact exists_affine_scheme_immersion_proper_ambient ((D.chart i).ι ≫ D.toBase ≫ f)
  choose P p e hp he hfac using h
  let l (i : Fin D.n) : D.common ⟶ P i := D.toChart i ≫ e i
  have hi (i : Fin D.n) : IsImmersion (l i) := by
    letI : IsOpenImmersion (D.toChart i) := D.toChart_open i
    letI : IsImmersion (e i) := he i
    dsimp [l]
    infer_instance
  have hcomm (i : Fin D.n) : l i ≫ p i = D.commonι ≫ D.toBase ≫ f := by
    dsimp [l]
    rw [Category.assoc, hfac i, ← Category.assoc (D.toChart i), D.toChart_fac i]
  obtain ⟨Z, j, q, π, hj, hd, hq, hπ, hjq, hbase, hproj⟩ :=
    exists_proper_graph_closure D.n D.n_pos P p hp (D.commonι ≫ D.toBase ≫ f) l hi hcomm
  exact ⟨P, p, e, Z, j, q, π, hp, he, hfac, hj, hd, hq, hπ, hjq, hbase, hproj⟩

end SerrePositivity.AlgebraicGeometry
