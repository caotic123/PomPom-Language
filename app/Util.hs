module Util where
import Data.Map

sLast :: [a] -> Maybe a
sLast [] = Nothing
sLast xs = Just $ last xs

type Bimap a k = (Map a k, Map k a)

insertBi :: (Ord k, Ord v) => k -> v -> Bimap k v -> Bimap k v
insertBi k v (a, b) = (Data.Map.insert k v a, Data.Map.insert v k b)

lookupLeftBi :: (Ord k, Ord v) => k -> Bimap k v -> Maybe v
lookupLeftBi k (a, b) = Data.Map.lookup k a

lookupRightBi :: (Ord k, Ord v) => v -> Bimap k v -> Maybe k
lookupRightBi k (a, b) = Data.Map.lookup k b

biInject :: (Ord k, Ord v) => (v -> v) -> k -> Bimap k v -> Bimap k v
biInject f k (a, b) = (Data.Map.update (Just . f) k a, let r = Data.Map.lookup k a in case r of
        Just r -> Data.Map.update (\_ -> Just k) (f r) b
        Nothing -> b)

emptyBi :: (Ord k, Ord v) => (Map k v, Map v k)
emptyBi = (Data.Map.empty, Data.Map.empty)

listBiLeft :: (Ord k, Ord v) => Bimap k v -> [(k, v)]
listBiLeft (a, b) = Data.Map.toList a