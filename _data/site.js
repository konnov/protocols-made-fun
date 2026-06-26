const fs = require("fs");
const yaml = require("js-yaml");

const config = yaml.load(fs.readFileSync("_config.yml", "utf8"));

module.exports = {
  ...config,
  title: config.title || "Protocols Made Fun",
  description: config.description || "",
  url: config.url || "https://protocols-made-fun.com",
  baseurl: "",
  feed: {
    path: "feed.xml",
    ...(config.feed || {}),
  },
};
