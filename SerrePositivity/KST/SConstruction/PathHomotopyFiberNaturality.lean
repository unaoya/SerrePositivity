module
public import SerrePositivity.KST.SConstruction.LoopHomotopyFiber
public import SerrePositivity.KST.Spectra.PathNaturality

/-! # path homotopy fiber と loop の比較の自然性
概要：可換正方形による path homotopy fiber の射と、loop からの包含の自然性を示す。
方針：二つの引き戻し射影を計算し、path の終点と loop の包含の既存の自然性を使う。
規約：Kan 性を使わない厳密な自然性。使われ方：反復経路の入力についての自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits
open Spectra

/-- 概要：点つき loop–fiber 同型は L9 の path への包含を回収する。
方針：底の射で既存の loop–fiber 同型の式を使う。
規約：点つき射の厳密等号。使われ方：引き戻しの第一射影の比較。 -/
lemma loopPointedPathFiberIso_hom_ι (B : PointedSimplicialSet.{u}) :
    (loopPointedPathFiberIso B).hom ≫ pointedFiberι (pathEndpoint B) =
      (loopToEndpointHomIso B).hom ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (pointedCofiberProjection _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}) B := by
  apply Under.UnderMorphism.ext
  exact loopBasedPathFiberIso_hom_ι B

/-- 概要：loop の homotopy fiber への包含の path 成分は L9 の path への包含。
方針：引き戻し fiber の逆比較の第一射影を計算する。
規約：strict な等号。使われ方：loop 比較の自然性。 -/
lemma loopToPathHomotopyFiber_path {E B : PointedSimplicialSet.{u}} (f : E ⟶ B) :
    loopToPathHomotopyFiber f ≫ pullback.fst (pathEndpoint B) f =
      (loopToEndpointHomIso B).hom ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (pointedCofiberProjection _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}) B := by
  change ((loopPointedPathFiberIso B).hom ≫
      pointedPullbackFiberFrom (pathEndpoint B) f ≫
      pointedFiberι (pullback.snd (pathEndpoint B) f)) ≫ pullback.fst _ _ = _
  rw [Category.assoc, pointedPullbackFiberFrom_ι, pullback.lift_fst,
    loopPointedPathFiberIso_hom_ι]

/-- 概要：点つき射の可換正方形が誘導する path homotopy fiber 間の射。
方針：path の後合成と元の源の射を引き戻しへ貼る。
規約：可換条件を明記し、選択は含まない。使われ方：入力の射の関手性。 -/
def pathHomotopyFiberMap {E B E' B' : PointedSimplicialSet.{u}}
    (f : E ⟶ B) (f' : E' ⟶ B') (a : E ⟶ E') (b : B ⟶ B') (h : f ≫ b = a ≫ f') :
    pathHomotopyFiber f ⟶ pathHomotopyFiber f' :=
  pullback.lift (pullback.fst (pathEndpoint B) f ≫ basedPathMap b)
    (pathHomotopyFiberProjection f ≫ a) (by
      rw [Category.assoc, pathEndpoint_natural, ← Category.assoc, pullback.condition,
        Category.assoc, h, ← Category.assoc]
      rfl)

/-- 概要：homotopy fiber の写像の path 成分。
方針：引き戻しの第一射影の回収式。
規約：任意の可換正方形。使われ方：関手法則と loop 比較。 -/
lemma pathHomotopyFiberMap_path {E B E' B' : PointedSimplicialSet.{u}}
    (f : E ⟶ B) (f' : E' ⟶ B') (a : E ⟶ E') (b : B ⟶ B') (h : f ≫ b = a ≫ f') :
    pathHomotopyFiberMap f f' a b h ≫ pullback.fst (pathEndpoint B') f' =
      pullback.fst (pathEndpoint B) f ≫ basedPathMap b := pullback.lift_fst ..

/-- 概要：homotopy fiber の写像の元の源への射影。
方針：引き戻しの第二射影の回収式。
規約：任意の可換正方形。使われ方：関手法則と loop 比較。 -/
lemma pathHomotopyFiberMap_projection {E B E' B' : PointedSimplicialSet.{u}}
    (f : E ⟶ B) (f' : E' ⟶ B') (a : E ⟶ E') (b : B ⟶ B') (h : f ≫ b = a ≫ f') :
    pathHomotopyFiberMap f f' a b h ≫ pathHomotopyFiberProjection f' =
      pathHomotopyFiberProjection f ≫ a := pullback.lift_snd ..

/-- 概要：loop から path homotopy fiber への包含は可換正方形について自然。
方針：path 成分は既存の loop–path 自然性、元の源への成分は零射で比較する。
規約：点つき射の厳密等号。使われ方：反復境界の自然な loop 比較。 -/
lemma loopToPathHomotopyFiber_naturality {E B E' B' : PointedSimplicialSet.{u}}
    (f : E ⟶ B) (f' : E' ⟶ B') (a : E ⟶ E') (b : B ⟶ B') (h : f ≫ b = a ≫ f') :
    loopToPathHomotopyFiber f ≫ pathHomotopyFiberMap f f' a b h =
      PointedObject.basedHomMap PointedSimplicialSet.circle.{u} b ≫ loopToPathHomotopyFiber f' := by
  apply pullback.hom_ext
  · calc
      _ = loopToPathHomotopyFiber f ≫
          (pullback.fst (pathEndpoint B) f ≫ basedPathMap b) := by
        rw [Category.assoc, pathHomotopyFiberMap_path]
      _ = ((loopToEndpointHomIso B).hom ≫
          _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (pointedCofiberProjection _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}) B) ≫
          basedPathMap b := by rw [← Category.assoc, loopToPathHomotopyFiber_path]
      _ = PointedObject.basedHomMap PointedSimplicialSet.circle.{u} b ≫
          ((loopToEndpointHomIso B').hom ≫
            _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (pointedCofiberProjection _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}) B') :=
        (loopToPath_natural b).symm
      _ = _ := by
        rw [Category.assoc]
        exact congrArg (fun k => PointedObject.basedHomMap PointedSimplicialSet.circle.{u} b ≫ k)
          (loopToPathHomotopyFiber_path f').symm
  · change (loopToPathHomotopyFiber f ≫ pathHomotopyFiberMap f f' a b h) ≫
        pathHomotopyFiberProjection f' =
      (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} b ≫ loopToPathHomotopyFiber f') ≫
        pathHomotopyFiberProjection f'
    calc
      _ = loopToPathHomotopyFiber f ≫ (pathHomotopyFiberProjection f ≫ a) := by
        rw [Category.assoc, pathHomotopyFiberMap_projection]
      _ = 0 := by rw [← Category.assoc, loopToPathHomotopyFiber_projection, zero_comp]
      _ = PointedObject.basedHomMap PointedSimplicialSet.circle.{u} b ≫
          (loopToPathHomotopyFiber f' ≫ pathHomotopyFiberProjection f') := by
        rw [loopToPathHomotopyFiber_projection, comp_zero]
      _ = _ := (Category.assoc _ _ _).symm

/-- 概要：恒等正方形の homotopy fiber の射は恒等射。
方針：二つの射影で比較し、path の後合成の恒等法則を使う。
規約：可換条件の証明に依存しない。使われ方：反復経路 fiber の関手法則。 -/
lemma pathHomotopyFiberMap_id {E B : PointedSimplicialSet.{u}} (f : E ⟶ B)
    (h : f ≫ 𝟙 B = 𝟙 E ≫ f) :
    pathHomotopyFiberMap f f (𝟙 E) (𝟙 B) h = 𝟙 (pathHomotopyFiber f) := by
  have hp : basedPathMap (𝟙 B) = 𝟙 (basedPathSpace B) :=
    (PointedObject.basedHomFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}).map_id B
  apply pullback.hom_ext
  · calc
      _ = pullback.fst (pathEndpoint B) f ≫ basedPathMap (𝟙 B) :=
        pathHomotopyFiberMap_path f f (𝟙 E) (𝟙 B) h
      _ = pullback.fst (pathEndpoint B) f := by rw [hp, Category.comp_id]
      _ = _ := (Category.id_comp _).symm
  · calc
      _ = pathHomotopyFiberProjection f ≫ 𝟙 E :=
        pathHomotopyFiberMap_projection f f (𝟙 E) (𝟙 B) h
      _ = _ := (Category.comp_id _).trans (Category.id_comp _).symm

/-- 概要：可換正方形の合成は homotopy fiber の射の合成に移る。
方針：二つの射影で比較し、path の後合成の合成法則を使う。
規約：合成の可換条件を明示する。使われ方：反復経路 fiber の関手法則。 -/
lemma pathHomotopyFiberMap_comp {E B E' B' E'' B'' : PointedSimplicialSet.{u}}
    (f : E ⟶ B) (f' : E' ⟶ B') (f'' : E'' ⟶ B'')
    (a : E ⟶ E') (b : B ⟶ B') (h : f ≫ b = a ≫ f')
    (a' : E' ⟶ E'') (b' : B' ⟶ B'') (h' : f' ≫ b' = a' ≫ f'')
    (h'' : f ≫ (b ≫ b') = (a ≫ a') ≫ f'') :
    pathHomotopyFiberMap f f' a b h ≫ pathHomotopyFiberMap f' f'' a' b' h' =
      pathHomotopyFiberMap f f'' (a ≫ a') (b ≫ b') h'' := by
  have hp : basedPathMap (b ≫ b') = basedPathMap b ≫ basedPathMap b' :=
    (PointedObject.basedHomFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}).map_comp b b'
  apply pullback.hom_ext
  · calc
      _ = (pathHomotopyFiberMap f f' a b h ≫ pullback.fst (pathEndpoint B') f') ≫
          basedPathMap b' := by
        rw [Category.assoc, pathHomotopyFiberMap_path, ← Category.assoc]
      _ = pullback.fst (pathEndpoint B) f ≫ (basedPathMap b ≫ basedPathMap b') := by
        rw [pathHomotopyFiberMap_path, Category.assoc]
      _ = pullback.fst (pathEndpoint B) f ≫ basedPathMap (b ≫ b') := by rw [hp]
      _ = _ := (pathHomotopyFiberMap_path f f'' (a ≫ a') (b ≫ b') h'').symm
  · change (pathHomotopyFiberMap f f' a b h ≫
        pathHomotopyFiberMap f' f'' a' b' h') ≫ pathHomotopyFiberProjection f'' =
      pathHomotopyFiberMap f f'' (a ≫ a') (b ≫ b') h'' ≫ pathHomotopyFiberProjection f''
    calc
      _ = (pathHomotopyFiberMap f f' a b h ≫ pathHomotopyFiberProjection f') ≫ a' := by
        rw [Category.assoc, pathHomotopyFiberMap_projection, ← Category.assoc]
      _ = pathHomotopyFiberProjection f ≫ (a ≫ a') := by
        rw [pathHomotopyFiberMap_projection, Category.assoc]
      _ = _ := (pathHomotopyFiberMap_projection f f'' (a ≫ a') (b ≫ b') h'').symm

end SerrePositivity.KST.SConstruction
