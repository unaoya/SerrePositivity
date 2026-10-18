module

public import SerrePositivity.InfinityCategories.F1.ScaffoldFiniteCylinder
public import SerrePositivity.InfinityCategories.F1.LeftScaffoldBaseChange

/-!
概要：有限鎖の写像円柱の比較の両端での計算。
方針：最初の辺上の組み立て射を頂点に制限し、終点では pushout の条件を使う。
規約：時刻零は最初の係数、時刻一は尾部の最初の係数に対応する。
使われ方：Kerodon Theorem 5.3.5.7、Theorem 5.2.4.1 の両端条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：組み立て射を定値の底で評価すると係数変換と定値包含の合成になる。
方針：定値射列と係数単体の Yoneda 表示を計算する。
規約：係数単体は第二成分として恒等に保つ。
使われ方：Kerodon Remark 5.3.2.12、Theorem 5.3.5.7、円柱の始点の計算。 -/
lemma simplicialReplacementAssembly_const
    {C : Type u} [Category.{u} C] {K : SSet.{u}} {F : C ⥤ SSet.{u}}
    (η : (CategoryTheory.Functor.const C).obj K ⟶ F) (c : C) :
    lift (SSet.const (nerveVertex c)) (𝟙 K) ≫ simplicialReplacementAssembly η =
      η.app c ≫ simplicialReplacementConstantLift F c := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  refine Sigma.ext (by rfl) ?_
  exact heq_of_eq (SSet.yonedaEquiv_symm_comp s (η.app c))

/-- 概要：最初の辺の prism の始点は零頂点に定値となる。
方針：最初の辺が零頂点を零頂点へ送ることを各次数で計算する。
規約：係数 K は変えない。
使われ方：Kerodon Theorem 5.3.5.7、零 fiber の比較への接続。 -/
lemma scaffoldFiniteFirstEdge_prism_zero (n : ℕ) (K : SSet.{u}) :
    prismEndpoint 0 K ≫
      (((stdSimplex.isoNerve 1).hom ≫ nerveMap (scaffoldFiniteFirstEdge n)) ▷ K) =
        lift (SSet.const (nerveVertex (ULift.up (0 : Fin (n + 2))))) (𝟙 K) := by
  rfl

/-- 概要：有限鎖の写像円柱の比較は始点で最初の係数の定値包含になる。
方針：区間部分の計算式に零頂点での組み立て射の計算を適用する。
規約：始点の包含は時刻零。
使われ方：Kerodon Theorem 5.3.5.7、最初の係数の fiber 比較との一致。 -/
lemma scaffoldFiniteCylinderComparison_endpoint_zero (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) :
    prismEndpoint 0 (F.obj (ULift.up 0)) ≫
      pushout.inl (prismEndpoint 1 (F.obj (ULift.up 0))) (scaffoldFiniteCylinderAttachingMap n F) ≫
      scaffoldFiniteCylinderComparison n F = simplicialReplacementConstantLift F (ULift.up 0) := by
  rw [scaffoldFiniteCylinderComparison_inl, ← Category.assoc, scaffoldFiniteFirstEdge_prism_zero]
  change lift _ _ ≫ simplicialReplacementAssembly
    (simplicialReplacementInitialCoefficient F (scaffoldFiniteInitial (n + 1))) = _
  rw [simplicialReplacementAssembly_const]
  change F.map ((scaffoldFiniteInitial (n + 1)).to (ULift.up 0)) ≫ _ = _
  rw [show (scaffoldFiniteInitial (n + 1)).to (ULift.up 0) = 𝟙 _ from
    (scaffoldFiniteInitial (n + 1)).hom_ext _ _, F.map_id, Category.id_comp]

/-- 概要：有限鎖の円柱の貼り合わせ射を全体へ含めると最初の構造射と定値包含になる。
方針：尾部の定値包含の底変換の計算を使う。
規約：全体の頂点一は尾部の頂点零。
使われ方：Kerodon Theorem 5.3.5.7、円柱の終点での比較。 -/
lemma scaffoldFiniteCylinderAttachingMap_baseMap (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) :
    scaffoldFiniteCylinderAttachingMap n F ≫ simplicialReplacementBaseMap (scaffoldFiniteTail n) F =
      (simplicialReplacementInitialCoefficient F (scaffoldFiniteInitial (n + 1))).app
        ((scaffoldFiniteTail n).obj (ULift.up 0)) ≫
          simplicialReplacementConstantLift F ((scaffoldFiniteTail n).obj (ULift.up 0)) := by
  rw [scaffoldFiniteCylinderAttachingMap, Category.assoc, simplicialReplacementConstantLift_baseMap]

/-- 概要：有限鎖の写像円柱の比較は終点で貼り合わせ射の全体への包含になる。
方針：pushout の可換条件の後に比較射の尾部での式を使う。
規約：構造射を適用してから尾部を全体へ含める。
使われ方：Kerodon Theorem 5.3.5.7、Theorem 5.2.4.1 の終点での整合性。 -/
lemma scaffoldFiniteCylinderComparison_endpoint_one (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) :
    prismEndpoint 1 (F.obj (ULift.up 0)) ≫
      pushout.inl (prismEndpoint 1 (F.obj (ULift.up 0))) (scaffoldFiniteCylinderAttachingMap n F) ≫
      scaffoldFiniteCylinderComparison n F =
        scaffoldFiniteCylinderAttachingMap n F ≫ simplicialReplacementBaseMap (scaffoldFiniteTail n) F := by
  rw [← Category.assoc, pushout.condition, Category.assoc, scaffoldFiniteCylinderComparison_inr]

end SerrePositivity.InfinityCategories
